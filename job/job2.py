# import subprocess
# def job_scheduling():
#     consts = ""
#     consts += "(declare-const T int)\n"
#     for i in range(0,11):
#         consts += f"(declare-const s{i} Int)\n"
#         consts += f"(declare-const f{i} Int)\n"
#         consts += f"(assert (>= s{i} 0))\n"
#         consts += f"(assert (= f{i} (+ s{i} {i})))\n"
#         consts += f"(assert (<= f{i} T))\n"
        
#         consts += f"(assert (and(>= s{3} f{2}) (>= s{3} f{1})))\n"
#         consts += f"(assert (and(>= s{6} f{2}) (>= s{6} f{4})))\n"
#         consts += f"(assert (and(>= s{7} f{1}) (>= s{7} f{4})))\n"
#         consts += f"(assert (>= s{7} f{5}))\n"
#         consts += f"(assert (and(>= s{8} f{3}) (>= s{8} f{6})))\n"
#         consts += f"(assert (and(>= s{9} f{6}) (>= s{9} f{7})))\n"
#         consts += f"(assert (and(>= s{10} f{8}) (>= s{10} f{9})))\n"
#     final = ""
    
#     final += "(declare-fun T () Int)\n"
#     final += "(minimize T)\n(check-sat)\n(get-model)\n(exit)\n"
        
#     print(final )
#     return final +consts
# # job_scheduling()
# smt_content = job_scheduling()
# with open("1.smt2", "w") as f:
#     f.write(smt_content)

# # Run Z3 on the generated file
# result = subprocess.run(["z3", "1.smt2"], capture_output=True, text=True)
# print(result.stdout)
import subprocess

def job_scheduling():
    consts = "(declare-const T Int)\n"
    
    for i in range(1, 11):
        consts += f"(declare-const S{i} Int)\n"
        consts += f"(declare-const E{i} Int)\n"
        consts += f"(assert (>= S{i} 0))\n"
        consts += f"(assert (= E{i} (+ S{i} {i+10})))\n"
        consts += f"(assert (<= E{i} T))\n"
    
    consts += "(assert (>= S3 E1))\n(assert (>= S3 E2))\n"
    consts += "(assert (>= S6 E2))\n(assert (>= S6 E4))\n"
    consts += "(assert (>= S7 E1))\n(assert (>= S7 E4))\n(assert (>= S7 E5))\n"
    consts += "(assert (>= S8 E3))\n(assert (>= S8 E6))\n"
    consts += "(assert (>= S9 E6))\n(assert (>= S9 E7))\n"
    consts += "(assert (>= S10 E8))\n(assert (>= S10 E9))\n"
    #q2
    consts += "(assert (>= S7 S8))"
    #q3 
    for (i, j) in [(3, 4), (3, 5), (4, 5)]:
        consts += f"(assert (or (<= E{i} S{j}) (<= E{j} S{i})))\n"
    final = "(minimize T)\n(check-sat)\n(get-model)\n(exit)\n"
    
    return consts + final

smt_content = job_scheduling()
with open("1.smt2", "w") as f:
    f.write(smt_content)

result = subprocess.run(["z3", "1.smt2"], capture_output=True, text=True)
print(result.stdout)