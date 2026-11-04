#!/usr/bin/env bash
set -euo pipefail
exec "$(dirname "$(realpath -e "${BASH_SOURCE[0]}")")/external" 2
