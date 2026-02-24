# Kubernetes Deployment for Eclexia

This directory contains Kubernetes manifests for deploying Eclexia in production.

## Prerequisites

- Kubernetes 1.27+ cluster
- kubectl configured
- 30GB+ available storage
- Carbon API keys (ElectricityMaps or WattTime)

## Quick Start

### 1. Create Namespace

```bash
kubectl apply -f namespace.yaml
```

### 2. Configure Secrets

**IMPORTANT:** Update `secret.yaml` with real API keys before applying!

```bash
# Option 1: Edit secret.yaml directly
vim secret.yaml

# Option 2: Create from files
kubectl create secret generic eclexia-secrets \
  --from-file=electricitymaps-api-key=./electricitymaps.key \
  --from-file=wattime-api-key=./wattime.key \
  --namespace=eclexia
```

### 3. Apply ConfigMap

```bash
kubectl apply -f configmap.yaml
```

### 4. Deploy StatefulSet

```bash
kubectl apply -f statefulset.yaml
```

### 5. Create Service

```bash
kubectl apply -f service.yaml
```

### 6. Verify Deployment

```bash
# Check pod status
kubectl get pods -n eclexia

# Check statefulset
kubectl get statefulset -n eclexia

# Check service
kubectl get svc -n eclexia

# View logs
kubectl logs -n eclexia eclexia-0
```

## Architecture

### Components

- **StatefulSet** - 3 replicas with persistent shadow price state
- **Service** - Load balancer with session affinity
- **ConfigMap** - Resource budgets and configuration
- **Secret** - Carbon API keys and credentials
- **PersistentVolumeClaims** - 10GB data + 5GB shadow prices per pod

### Persistence

Each pod has two persistent volumes:
1. **data** (10GB) - General application data
2. **shadow-prices** (5GB) - Shadow price state (critical)

Shadow prices are preserved across pod restarts to maintain economic continuity.

## Configuration

### Resource Budgets

Edit `configmap.yaml` to adjust default resource budgets:

```toml
[energy]
budget = "10000J"
shadow_price_base = 0.01
shadow_price_multiplier = 5.0
```

### Replicas

Scale up/down:

```bash
kubectl scale statefulset eclexia --replicas=5 -n eclexia
```

### Resource Limits

Adjust in `statefulset.yaml`:

```yaml
resources:
  requests:
    cpu: 250m
    memory: 512Mi
  limits:
    cpu: 1000m
    memory: 1Gi
```

## Monitoring

### Health Checks

- **Liveness:** `GET /health` (port 8080)
- **Readiness:** `GET /ready` (port 8080)

### Metrics

Prometheus metrics exposed on port 9090:

```bash
kubectl port-forward -n eclexia eclexia-0 9090:9090
curl http://localhost:9090/metrics
```

## Troubleshooting

### Pods Not Starting

```bash
# Describe pod
kubectl describe pod -n eclexia eclexia-0

# Check events
kubectl get events -n eclexia --sort-by='.lastTimestamp'

# Check logs
kubectl logs -n eclexia eclexia-0
```

### Persistent Volume Issues

```bash
# Check PVCs
kubectl get pvc -n eclexia

# Check PVs
kubectl get pv | grep eclexia
```

### Secret Issues

```bash
# Verify secret exists
kubectl get secret eclexia-secrets -n eclexia

# Check secret contents (keys only)
kubectl describe secret eclexia-secrets -n eclexia
```

## Upgrading

### Rolling Update

```bash
# Update image
kubectl set image statefulset/eclexia \
  eclexia=ghcr.io/hyperpolymath/eclexia:v0.2.0 \
  -n eclexia

# Watch rollout
kubectl rollout status statefulset/eclexia -n eclexia
```

### Rollback

```bash
# Rollback to previous version
kubectl rollout undo statefulset/eclexia -n eclexia
```

## Backup and Restore

### Backup Shadow Prices

```bash
# Backup from pod
kubectl exec -n eclexia eclexia-0 -- \
  tar czf - /var/lib/eclexia/shadow-prices \
  > shadow-prices-backup.tar.gz
```

### Restore Shadow Prices

```bash
# Restore to pod
kubectl exec -i -n eclexia eclexia-0 -- \
  tar xzf - -C / \
  < shadow-prices-backup.tar.gz
```

## Production Checklist

- [ ] Real API keys in secret.yaml
- [ ] Storage class configured
- [ ] Resource limits appropriate for workload
- [ ] Monitoring and alerting set up
- [ ] Backup strategy in place
- [ ] Network policies configured
- [ ] RBAC permissions reviewed
- [ ] TLS certificates configured (if external)

## Security

### Network Policies

Apply network policies to restrict traffic:

```bash
kubectl apply -f network-policy.yaml
```

### RBAC

Create service account with minimal permissions:

```bash
kubectl apply -f rbac.yaml
```

### Pod Security

Pods run as non-root user (UID 1000) with read-only root filesystem.

## Clean Up

```bash
# Delete all resources
kubectl delete namespace eclexia

# Or delete individually
kubectl delete statefulset eclexia -n eclexia
kubectl delete service eclexia eclexia-headless -n eclexia
kubectl delete configmap eclexia-config -n eclexia
kubectl delete secret eclexia-secrets -n eclexia
kubectl delete pvc -l app.kubernetes.io/name=eclexia -n eclexia
```

## Support

- **Documentation:** https://eclexia.org/docs/deployment
- **Issues:** https://github.com/hyperpolymath/eclexia/issues
- **Community:** Discord server

---

**License:** PMPL-1.0-or-later
**Maintainer:** Jonathan D.A. Jewell
