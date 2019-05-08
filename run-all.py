#!/usr/local/bin/python3

import sys
import subprocess

lemma_synth_configs = [
  ("", 
    [
      "Nat/plus_assoc",
      "Nat/plus_comm",
      "Nat/mult_assoc",
      "CLAM/goal2",
      "CLAM/goal3",
      "CLAM/goal4",
      "CLAM/goal7",
      "CLAM/goal8",
      "CLAM/goal9",
      "CLAM/goal22",
      "CLAM/goal23",
      "CLAM/goal24",
      "CLAM/goal25",
      "CLAM/goal26",
      "CLAM/goal27",
      "CLAM/goal28",
      "CLAM/goal45",
      "CLAM/goal46",
      "CLAM/goal47",
      "CLAM/goal51",
      "CLAM/goal52",
      "CLAM/goal53",
      "CLAM/goal54",
      "CLAM/goal57",
      "CLAM/goal58",
      "CLAM/goal59",
      "CLAM/goal60",
      "CLAM/goal61",
      "CLAM/goal63",
      "CLAM/goal64",
      "CLAM/goal65",
      "CLAM/goal66",
      "CLAM/goal67",
      "CLAM/goal68",
      "CLAM/goal69",
      "CLAM/goal71",
      "CLAM/goal72",
      "CLAM/goal74",
      "CLAM/goal75",
      "CLAM/goal76",
      "LEON/amortize-queue-goal1",
      "LEON/amortize-queue-goal2",
      "LEON/amortize-queue-goal3",
      "LEON/amortize-queue-goal4",
      # "LEON/amortize-queue-goal6",
      "LEON/amortize-queue-goal8",
      "LEON/amortize-queue-goal10",
      "LEON/amortize-queue-goal11",
      "LEON/amortize-queue-goal12",
      "LEON/amortize-queue-goal15",
      # "LEON/bsearch-tree-goal1",
      # "LEON/bsearch-tree-goal3",
      "TIP/bin_plus_comm",
      "TIP/list_append_inj_1",
      "TIP/list_Interleave",
      "TIP/list_weird_is_normal",
      "TIP/nat_acc_plus_assoc",
      "TIP/nat_acc_plus_comm",
      "TIP/nat_acc_plus_same",
      "TIP/nat_pow_one",
      # "TIP/rotate_snoc_self",
      # "TIP/rotate_snoc",
      "TIP/weird_nat_add3_assoc1",
      "TIP/weird_nat_add3_assoc2",
      "TIP/weird_nat_add3_assoc3",
      "TIP/weird_nat_add3_comm12",
      "TIP/weird_nat_add3_comm13",
      "TIP/weird_nat_add3_comm23",
      "TIP/weird_nat_add3_rot",
      "TIP/weird_nat_add3_rrot",
      "TIP/weird_nat_add3_same",
      "TIP/weird_nat_add3acc_assoc1",
      "TIP/weird_nat_add3acc_assoc2",
      "TIP/weird_nat_add3acc_assoc3",
      "TIP/weird_nat_add3acc_comm12",
      "TIP/weird_nat_add3acc_rot",
    ]),
  ("--try-assoc",
    [ 
      "CLAM/goal10",
      "CLAM/goal11",
      "CLAM/goal18",
      "CLAM/goal19",
      "CLAM/goal21",
      "CLAM/goal29",
      "CLAM/goal32",
      "CLAM/goal77",
      "CLAM/goal80",
      "CLAM/goal81",
      "CLAM/goal83",
      "TIP/tree_Flatten2",
    ]),
  ("--try-comm",
    [ 
      "CLAM/goal1",
      "CLAM/goal13",
      "CLAM/goal15",
      "TIP/bin_s",
    ]),
  ("--try-comm --try-assoc",
    [ 
      "Nat/mult_comm",
    ]),
  ("--gen-fapp 1",
    [ 
      "CLAM/goal5",
      "CLAM/goal6",
      "CLAM/goal12",
    ]),
  ("--gen-fapp 3",
    [ 
      "Nat/distribute",
    ]),
  ("--term-depth 4",
    [ 
      "CLAM/goal20",
    ]),
  ("--more-fail", 
    [
      "CLAM/goal16",
    ]),
  # ("--try-assoc --gen-fapp 1",
  #   [
  #     "CLAM/goal82",
  #   ]),
  ("--try-assoc --gen-fapp 2",
    [
      "CLAM/goal30",
    ]),
]

cvc4_command = ['cvc4-1.7', '--tlimit=300000', '--quant-ind', '--quant-cf', '--conjecture-gen', '--conjecture-gen-per-round=3', '--full-saturate-quant', '--lang=smt2.0']

exe_path = 'build/tools/adt/ind'
extra_args = ''
file_path = 'bench_adt/'
file_ext = '.smt2'

log_path = 'logs/'

def main():
    for config, file_list in lemma_synth_configs:
      for file_name in file_list:
        real_fname = file_path+file_name+file_ext
        print("Running ", exe_path, config, real_fname)
        log_file = open(log_path+file_name+'.log', 'w')
        ret = subprocess.call([exe_path, *((config + ' ' + extra_args).split()), real_fname], stdout=log_file)
        if ret == 0:
          print("Success")
        else:
          print("Failed")
        log_file.close()

if __name__ == '__main__':
    main()