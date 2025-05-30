import subprocess

def truck_delivery():
    consts = ""
    
    # Number of trucks
    num_trucks = 8
    # Number of trucks with cooling facility
    cooling_trucks = 3
    
    # Declare variables for each truck and pallet type
    # nuzzles[i] = number of nuzzle pallets in truck i
    # prittles[i] = number of prittle pallets in truck i  
    # skipples[i] = number of skipple pallets in truck i
    # crottles[i] = number of crottle pallets in truck i
    # dupples[i] = number of dupple pallets in truck i
    
    for i in range(1, num_trucks + 1):
        consts += f"(declare-const nuzzles{i} Int)\n"
        consts += f"(declare-const prittles{i} Int)\n"
        consts += f"(declare-const skipples{i} Int)\n"
        consts += f"(declare-const crottles{i} Int)\n"
        consts += f"(declare-const dupples{i} Int)\n"
        
        # All variables must be non-negative
        consts += f"(assert (>= nuzzles{i} 0))\n"
        consts += f"(assert (>= prittles{i} 0))\n"
        consts += f"(assert (>= skipples{i} 0))\n"
        consts += f"(assert (>= crottles{i} 0))\n"
        consts += f"(assert (>= dupples{i} 0))\n"
        
        # Weight constraint: each truck can carry at most 8000 kg
        consts += f"(assert (<= (+ (* nuzzles{i} 800) (* prittles{i} 1100) (* skipples{i} 1000) (* crottles{i} 2500) (* dupples{i} 200)) 8000))\n"
        
        # Pallet count constraint: each truck can carry at most 8 pallets
        consts += f"(assert (<= (+ nuzzles{i} prittles{i} skipples{i} crottles{i} dupples{i}) 8))\n"
        
        # Nuzzles constraint: no two pallets of nuzzles in the same truck
        consts += f"(assert (<= nuzzles{i} 1))\n"
    
    # Total delivery requirements
    # Four pallets of nuzzles
    consts += "(assert (= (+ "
    for i in range(1, num_trucks + 1):
        consts += f"nuzzles{i} "
    consts += ") 4))\n"
    
    # Eight pallets of skipples
    consts += "(assert (= (+ "
    for i in range(1, num_trucks + 1):
        consts += f"skipples{i} "
    consts += ") 8))\n"
    
    # Ten pallets of crottles
    consts += "(assert (= (+ "
    for i in range(1, num_trucks + 1):
        consts += f"crottles{i} "
    consts += ") 10))\n"
    
    # Twenty pallets of dupples
    consts += "(assert (= (+ "
    for i in range(1, num_trucks + 1):
        consts += f"dupples{i} "
    consts += ") 20))\n"
    
    # Skipples cooling constraint: only trucks 1, 2, 3 can carry skipples
    for i in range(4, num_trucks + 1):
        consts += f"(assert (= skipples{i} 0))\n"
    
    # Declare variable for total prittles
    consts += "(declare-const total_prittles Int)\n"
    consts += "(assert (= total_prittles (+ "
    for i in range(1, num_trucks + 1):
        consts += f"prittles{i} "
    consts += ")))\n"
    
    # Question 2: Prittles and crottles cannot be in the same truck
    # Uncomment the following lines for question 2
    # for i in range(1, num_trucks + 1):
    #     consts += f"(assert (or (= prittles{i} 0) (= crottles{i} 0)))\n"
    
    # Maximize total prittles
    final = "(maximize total_prittles)\n(check-sat)\n(get-model)\n(exit)\n"
    
    return consts + final

def truck_delivery_q2():
    consts = ""
    
    # Number of trucks
    num_trucks = 8
    # Number of trucks with cooling facility
    cooling_trucks = 3
    
    # Declare variables for each truck and pallet type
    for i in range(1, num_trucks + 1):
        consts += f"(declare-const nuzzles{i} Int)\n"
        consts += f"(declare-const prittles{i} Int)\n"
        consts += f"(declare-const skipples{i} Int)\n"
        consts += f"(declare-const crottles{i} Int)\n"
        consts += f"(declare-const dupples{i} Int)\n"
        
        # All variables must be non-negative
        consts += f"(assert (>= nuzzles{i} 0))\n"
        consts += f"(assert (>= prittles{i} 0))\n"
        consts += f"(assert (>= skipples{i} 0))\n"
        consts += f"(assert (>= crottles{i} 0))\n"
        consts += f"(assert (>= dupples{i} 0))\n"
        
        # Weight constraint: each truck can carry at most 8000 kg
        consts += f"(assert (<= (+ (* nuzzles{i} 800) (* prittles{i} 1100) (* skipples{i} 1000) (* crottles{i} 2500) (* dupples{i} 200)) 8000))\n"
        
        # Pallet count constraint: each truck can carry at most 8 pallets
        consts += f"(assert (<= (+ nuzzles{i} prittles{i} skipples{i} crottles{i} dupples{i}) 8))\n"
        
        # Nuzzles constraint: no two pallets of nuzzles in the same truck
        consts += f"(assert (<= nuzzles{i} 1))\n"
        
        # Question 2: Prittles and crottles cannot be in the same truck
        consts += f"(assert (or (= prittles{i} 0) (= crottles{i} 0)))\n"
    
    # Total delivery requirements
    # Four pallets of nuzzles
    consts += "(assert (= (+ "
    for i in range(1, num_trucks + 1):
        consts += f"nuzzles{i} "
    consts += ") 4))\n"
    
    # Eight pallets of skipples
    consts += "(assert (= (+ "
    for i in range(1, num_trucks + 1):
        consts += f"skipples{i} "
    consts += ") 8))\n"
    
    # Ten pallets of crottles
    consts += "(assert (= (+ "
    for i in range(1, num_trucks + 1):
        consts += f"crottles{i} "
    consts += ") 10))\n"
    
    # Twenty pallets of dupples
    consts += "(assert (= (+ "
    for i in range(1, num_trucks + 1):
        consts += f"dupples{i} "
    consts += ") 20))\n"
    
    # Skipples cooling constraint: only trucks 1, 2, 3 can carry skipples
    for i in range(4, num_trucks + 1):
        consts += f"(assert (= skipples{i} 0))\n"
    
    # Declare variable for total prittles
    consts += "(declare-const total_prittles Int)\n"
    consts += "(assert (= total_prittles (+ "
    for i in range(1, num_trucks + 1):
        consts += f"prittles{i} "
    consts += ")))\n"
    
    # Maximize total prittles
    final = "(maximize total_prittles)\n(check-sat)\n(get-model)\n(exit)\n"
    
    return consts + final

import re

def extract_total_prittles(z3_output):
    """Extract the total_prittles value from Z3 output"""
    match = re.search(r'\(define-fun total_prittles \(\) Int\s+(\d+)\)', z3_output)
    if match:
        return int(match.group(1))
    return None

print("TRUCK DELIVERY OPTIMIZATION")
print("=" * 40)

print("\nQuestion 1: Maximum prittles without explosive constraint")
smt_content = truck_delivery()
with open("trucks_q1.smt2", "w") as f:
    f.write(smt_content)

result = subprocess.run(["z3", "trucks_q1.smt2"], capture_output=True, text=True)
total_q1 = extract_total_prittles(result.stdout)
if total_q1 is not None:
    print(f"Answer: {total_q1}")
else:
    print("Could not extract result")

print("\nQuestion 2: Maximum prittles with explosive constraint")
smt_content_q2 = truck_delivery_q2()
with open("trucks_q2.smt2", "w") as f:
    f.write(smt_content_q2)

result2 = subprocess.run(["z3", "trucks_q2.smt2"], capture_output=True, text=True)
total_q2 = extract_total_prittles(result2.stdout)
if total_q2 is not None:
    print(f"Answer: {total_q2}")
else:
    print("Could not extract result")
