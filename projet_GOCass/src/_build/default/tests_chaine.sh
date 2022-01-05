#!/bin/bash
for l in ../tests/bad_old/*.go; do echo $l; ./pgoc --debug --type-only $l; done
for l in ../tests/good_old/*.go; do echo $l; ./pgoc --debug --type-only $l; done
for l in ../tests/bad/*/*.go; do echo $l; ./pgoc --debug --type-only $l; done
for l in ../tests/good/*/*.go; do echo $l; ./pgoc --debug --type-only $l; done
