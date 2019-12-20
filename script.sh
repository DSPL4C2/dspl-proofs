#!/bin/bash

mkdir artifacts
mkdir artifacts/presentations
mkdir references
mkdir reports

touch README.MD
touch artifacts/README.MD
touch artifacts/presentations/README.MD
touch references/README.MD
touch reports/README.MD

git add .
git commit  -m "Initial folders structure is provided."

