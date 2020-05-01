#!/bin/bash

run_test() {
  out=$(dist/build/runiml/runiml $1 --silent);
  if [[ $out ]]
    then  echo $1:;
          echo "$out";
  fi
}
export -f run_test
find examples -name "*.iml" | xargs -n1 -I{} bash -c 'run_test "$@"' _ {} 
