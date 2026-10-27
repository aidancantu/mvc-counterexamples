#!/bin/sh
# Build the actual theorems; serialize expensive witnesses to limit memory use.
set -eu
cd "$(dirname "$0")"
for degree in 2650 2725 2798 2840 2917; do
  lake build "Mvc.Witnesses.Degree${degree}"
done
lake build
lake env lean Mvc/AxiomAudit.lean
