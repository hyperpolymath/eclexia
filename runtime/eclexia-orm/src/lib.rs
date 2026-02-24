// SPDX-License-Identifier: PMPL-1.0-or-later

//! Lightweight parameterized SQL query builder.

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Null,
    Bool(bool),
    Int(i64),
    Float(f64),
    Text(String),
}

impl From<&str> for Value {
    fn from(value: &str) -> Self {
        Self::Text(value.to_string())
    }
}

impl From<String> for Value {
    fn from(value: String) -> Self {
        Self::Text(value)
    }
}

impl From<i64> for Value {
    fn from(value: i64) -> Self {
        Self::Int(value)
    }
}

impl From<bool> for Value {
    fn from(value: bool) -> Self {
        Self::Bool(value)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Query {
    pub sql: String,
    pub params: Vec<Value>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Kind {
    Select,
    Insert,
    Update,
    Delete,
}

#[derive(Debug, Clone)]
pub struct QueryBuilder {
    kind: Kind,
    table: String,
    select_columns: Vec<String>,
    insert_values: Vec<(String, Value)>,
    update_values: Vec<(String, Value)>,
    where_clauses: Vec<(String, Value)>,
    order_by: Option<(String, bool)>,
    limit: Option<usize>,
}

impl QueryBuilder {
    pub fn select(table: &str, columns: &[&str]) -> Self {
        Self {
            kind: Kind::Select,
            table: table.to_string(),
            select_columns: columns.iter().map(|c| (*c).to_string()).collect(),
            insert_values: Vec::new(),
            update_values: Vec::new(),
            where_clauses: Vec::new(),
            order_by: None,
            limit: None,
        }
    }

    pub fn insert(table: &str) -> Self {
        Self {
            kind: Kind::Insert,
            table: table.to_string(),
            select_columns: Vec::new(),
            insert_values: Vec::new(),
            update_values: Vec::new(),
            where_clauses: Vec::new(),
            order_by: None,
            limit: None,
        }
    }

    pub fn update(table: &str) -> Self {
        Self {
            kind: Kind::Update,
            table: table.to_string(),
            select_columns: Vec::new(),
            insert_values: Vec::new(),
            update_values: Vec::new(),
            where_clauses: Vec::new(),
            order_by: None,
            limit: None,
        }
    }

    pub fn delete(table: &str) -> Self {
        Self {
            kind: Kind::Delete,
            table: table.to_string(),
            select_columns: Vec::new(),
            insert_values: Vec::new(),
            update_values: Vec::new(),
            where_clauses: Vec::new(),
            order_by: None,
            limit: None,
        }
    }

    pub fn value(mut self, column: &str, value: impl Into<Value>) -> Self {
        self.insert_values.push((column.to_string(), value.into()));
        self
    }

    pub fn set(mut self, column: &str, value: impl Into<Value>) -> Self {
        self.update_values.push((column.to_string(), value.into()));
        self
    }

    pub fn where_eq(mut self, column: &str, value: impl Into<Value>) -> Self {
        self.where_clauses.push((column.to_string(), value.into()));
        self
    }

    pub fn order_by(mut self, column: &str, desc: bool) -> Self {
        self.order_by = Some((column.to_string(), desc));
        self
    }

    pub fn limit(mut self, n: usize) -> Self {
        self.limit = Some(n);
        self
    }

    pub fn build(self) -> Result<Query, String> {
        match self.kind {
            Kind::Select => self.build_select(),
            Kind::Insert => self.build_insert(),
            Kind::Update => self.build_update(),
            Kind::Delete => self.build_delete(),
        }
    }

    fn build_select(self) -> Result<Query, String> {
        let mut sql = String::new();
        let cols = if self.select_columns.is_empty() {
            "*".to_string()
        } else {
            self.select_columns.join(", ")
        };
        sql.push_str(&format!("SELECT {} FROM {}", cols, self.table));

        let mut params = Vec::new();
        append_where(&mut sql, &self.where_clauses, &mut params);
        if let Some((col, desc)) = self.order_by {
            sql.push_str(&format!(
                " ORDER BY {} {}",
                col,
                if desc { "DESC" } else { "ASC" }
            ));
        }
        if let Some(limit) = self.limit {
            sql.push_str(&format!(" LIMIT {}", limit));
        }
        Ok(Query { sql, params })
    }

    fn build_insert(self) -> Result<Query, String> {
        if self.insert_values.is_empty() {
            return Err("insert requires at least one value".to_string());
        }

        let mut columns = Vec::new();
        let mut params = Vec::new();
        for (col, value) in self.insert_values {
            columns.push(col);
            params.push(value);
        }
        let placeholders = vec!["?"; columns.len()].join(", ");
        let sql = format!(
            "INSERT INTO {} ({}) VALUES ({})",
            self.table,
            columns.join(", "),
            placeholders
        );
        Ok(Query { sql, params })
    }

    fn build_update(self) -> Result<Query, String> {
        if self.update_values.is_empty() {
            return Err("update requires at least one set() value".to_string());
        }
        let mut sql = format!("UPDATE {} SET ", self.table);
        let mut params = Vec::new();

        for (idx, (col, value)) in self.update_values.into_iter().enumerate() {
            if idx > 0 {
                sql.push_str(", ");
            }
            sql.push_str(&format!("{} = ?", col));
            params.push(value);
        }

        append_where(&mut sql, &self.where_clauses, &mut params);
        if let Some(limit) = self.limit {
            sql.push_str(&format!(" LIMIT {}", limit));
        }
        Ok(Query { sql, params })
    }

    fn build_delete(self) -> Result<Query, String> {
        let mut sql = format!("DELETE FROM {}", self.table);
        let mut params = Vec::new();
        append_where(&mut sql, &self.where_clauses, &mut params);
        if let Some(limit) = self.limit {
            sql.push_str(&format!(" LIMIT {}", limit));
        }
        Ok(Query { sql, params })
    }
}

fn append_where(sql: &mut String, where_clauses: &[(String, Value)], params: &mut Vec<Value>) {
    if where_clauses.is_empty() {
        return;
    }
    sql.push_str(" WHERE ");
    for (idx, (col, value)) in where_clauses.iter().enumerate() {
        if idx > 0 {
            sql.push_str(" AND ");
        }
        sql.push_str(&format!("{} = ?", col));
        params.push(value.clone());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn expect_ok<T, E: std::fmt::Debug>(res: Result<T, E>) -> T {
        match res {
            Ok(v) => v,
            Err(e) => panic!("expected ok, got {:?}", e),
        }
    }

    #[test]
    fn test_select_builder() {
        let q = expect_ok(
            QueryBuilder::select("users", &["id", "name"])
                .where_eq("role", "admin")
                .order_by("id", true)
                .limit(10)
                .build(),
        );
        assert_eq!(
            q.sql,
            "SELECT id, name FROM users WHERE role = ? ORDER BY id DESC LIMIT 10"
        );
        assert_eq!(q.params, vec![Value::Text("admin".to_string())]);
    }

    #[test]
    fn test_insert_builder() {
        let q = expect_ok(
            QueryBuilder::insert("users")
                .value("name", "Ada")
                .value("active", true)
                .build(),
        );
        assert_eq!(q.sql, "INSERT INTO users (name, active) VALUES (?, ?)");
        assert_eq!(q.params.len(), 2);
    }

    #[test]
    fn test_update_builder() {
        let q = expect_ok(
            QueryBuilder::update("users")
                .set("name", "Grace")
                .where_eq("id", 7i64)
                .build(),
        );
        assert_eq!(q.sql, "UPDATE users SET name = ? WHERE id = ?");
        assert_eq!(
            q.params,
            vec![Value::Text("Grace".to_string()), Value::Int(7)]
        );
    }
}
