#!/bin/bash -eux

cat >>$HOME/.bashrc <<'EOF'
export PATH=$HOME/.nix-profile/bin:$PATH
EOF
source $HOME/.bashrc


echo "## Checking installation"

which idris2
idris2 --prefix
idris2 --paths
idris2 --libdir

echo "## Installing Artifact"

cd /tmp/
tar -zxvf /tmp/velo.tar.gz

cd "$HOME"
mv /tmp/velo "$HOME/velo"

echo "## Testing Artifact"

cd "velo"

make velo
make velo-test-run

cd "$HOME"

echo "## Finished"
