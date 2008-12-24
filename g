#!/bin/sh
set -e
ghc --make -odir dist/build -hidir dist/build -idist/build:src src/Test.hs -main-is Test.runTests -o test
./test
rm test
hsb
cd ~/g/ch/chia
big chia
