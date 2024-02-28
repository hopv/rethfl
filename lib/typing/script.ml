let prepare_fptprove_script () =
  let save_string path buf =
    let oc = open_out path in
    Printf.fprintf oc "%s" buf;
    close_out oc;
    path
  in
  let sub_script = {|
    is_mac () {
      sw_vers > /dev/null 2>&1
      return $?
    }

    if is_mac ; then
          date='gdate'
    else
          date='date'
    fi

    # Note that timeout changes its process group, so timeout cannot recieve SIGINT from a terminal.
    # Note also that when ocaml invokes z3, SIGINT terminates not the whole program but just z3.
    function interruptible_timeout() {
      timeout $@ &
      pgid=$!
      # NOTE: when a script executed from another script, the INT signal will not be passed
      trap "kill -TERM -$pgid" EXIT
      wait $pgid
    }

    function nanosec2sec() {
      sed -E 's/(.{9})$/.\1/' <<< "$1" | sed -E 's/^0*(0|([1-9][0-9]*))\./\1./'
    }

    start_time=$($date +%s%N)
    output=`interruptible_timeout $@`

    exit_code=$?

    if [ $exit_code = 124 ]; then
      end_time=$($date +%s%N)
      elapsed=$(nanosec2sec "0000000000$((end_time - start_time))")
        echo "${@:$#:1},timeout,$elapsed"
        exit
    fi

    if [ $exit_code != 0 ]; then
      echo "ERROR"
      echo $exit_code
      exit
    fi

    echo "OK!!!"

    IFS="," read result iterations <<< "$output"

    end_time=$($date +%s%N)
    elapsed=$(nanosec2sec "0000000000$((end_time - start_time))")

    if      [ "$result" = "valid" ] ||
            [ "$result" = "invalid" ] ||
            [ "$result" = "sat" ] ||
            [ "$result" = "unsat" ] ||
            [ "$result" = "unknown" ] ||
            [ "$result" = "infeasible" ] ||
            [ "$result" = "YES" ] ||
            [ "$result" = "NO" ] ||
            [ "$result" = "MAYBE" ]; then

            echo "${@:$#:1},$result,$elapsed,$iterations"
    else
            echo "${@:$#:1},abort,$elapsed,$iterations"
    fi
  |} in
  let sub_script_path = Hflmc2_util.gen_temp_filename "/tmp/fptprove_launch_script_para_aux_" ".sh" in
  let fptprove_output_path = Hflmc2_util.gen_temp_filename "/tmp/fptprove_output1" "" in
  ignore @@ save_string sub_script_path sub_script;
  let script = {|
    cd $2
    timeout=$3
    options='-p pcsp'
    setsid /bin/bash -c "/bin/bash |} ^ sub_script_path ^ {| $timeout $2/_build/default/main.exe -c $2/config/$4 $options $1 > |} ^ fptprove_output_path ^ {|" &
    pgid1=$!

    trap "kill -TERM -$pgid1" EXIT

    while :
    do
        alive1=$(ps -ef | grep " $pgid1 " | grep -v grep | awk '{ print $2 }')
        if [ -z "$alive1" ]; then
            cat |} ^ fptprove_output_path ^ {|
            break
        fi
        sleep 0.5
    done
  |} in
  let script_path = save_string (Hflmc2_util.gen_temp_filename "/tmp/fptprove_launch_script_" ".sh") script in
  script_path
