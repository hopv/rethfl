import sys, time, subprocess

try:
    start = time.time()
    res = subprocess.check_output(sys.argv[1:], timeout=100)
    end = time.time()
    print("time: %f" % (end - start))
except:
    print('timeout')