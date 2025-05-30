import subprocess
import re

def generate_smt_constraints():
    n = 10
    smt_code = """
(declare-const n Int)
(assert (and (>= n 1) (<= n 10)))

(declare-const a0 Int)
(declare-const b0 Int)
(assert (= a0 1))
(assert (= b0 1))
"""
    
    for i in range(1, n + 1):
        smt_code += f"""
(declare-const a{i} Int)
(declare-const b{i} Int)
(declare-const c{i} Bool)
(assert (ite c{i}
        (and (= a{i} (+ a{i-1} (* 2 b{i-1}))) (= b{i} (+ b{i-1} {i})))
        (and (= a{i} (+ a{i-1} {i})) (= b{i} (+ a{i-1} b{i-1})))))
"""
    
    smt_code += f"""
(assert (= b{n} (+ 600 n)))
(check-sat)
(get-model)
(exit)
"""
    
    return smt_code

ans = []
for n in range(1, 11):
    with open("1.smt2", "w") as f:
        f.write(generate_smt_constraints().replace("(declare-const n Int)", f"(declare-const n Int)\n(assert (= n {n}))"))
    
    result = subprocess.run(["z3", "1.smt2"], capture_output=True, text=True)
    output = result.stdout
    
    if "unsat" in output:
        ans.append(str(n))
    else:
        match = re.search(r'\(define-fun n \(\) Int\s+(\d+)\)', output)
        if match:
            found_n = match.group(1)
            with open("1.smt2", "w") as f:
                f.write(generate_smt_constraints().replace("(declare-const n Int)", f"(declare-const n Int)\n(assert (not (= n {found_n})))"))
                
            result = subprocess.run(["z3", "1.smt2"], capture_output=True, text=True)
            output = result.stdout
            if "unsat" in output:
                ans.append(str(n))

print("".join(ans))
