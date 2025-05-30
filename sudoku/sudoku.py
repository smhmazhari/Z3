# Modified Sudoku Solver with Enhanced Visualization
import argparse
import subprocess
import re
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.patches import Rectangle

def generate_smt2(smt2_filename):
    # Embedded puzzle data (9x9 grid, '-' means empty cell)
    puzzle_data = [
        "- - - - - - - - -",
        "- - - - - - - - -",
        "- - - - - - - - -",
        "- - - - - - - - -",
        "- - - - - - - - -",
        "- - - - - - - - -",
        "- - - - - - - - -",
        "- - - - - - - - -",
        "- - - - - - - - -"
    ]
    
    # Embedded LQ (inequality) constraints
    lq_constraints = [
        "2,4 - 2,5", "2,5 - 2,6", "2,6 - 2,7", "2,7 - 2,8", "2,8 - 2,9",
        "4,1 - 4,2", "4,2 - 4,3", "4,3 - 4,4", "4,4 - 4,5", "4,5 - 4,6",
        "6,4 - 6,5", "6,5 - 6,6", "6,6 - 6,7", "6,7 - 6,8", "6,8 - 6,9",
        "8,1 - 8,2", "8,2 - 8,3", "8,3 - 8,4", "8,4 - 8,5", "8,5 - 8,6"
    ]
    
    # Embedded consecutive constraints
    consecutive_constraints = [
        "1,2 - 1,3", "1,4 - 1,5", "1,7 - 1,8", "1,6 - 2,6", "2,7 - 3,7",
        "3,2 - 3,3", "3,4 - 3,5", "3,5 - 3,6", "3,7 - 4,7", "3,9 - 4,9",
        "4,3 - 5,3", "4,9 - 5,9", "4,7 - 5,7", "5,1 - 5,2", "5,2 - 5,3",
        "5,4 - 5,5", "5,6 - 5,7", "5,8 - 5,9", "6,3 - 6,4", "6,3 - 7,3",
        "6,4 - 7,4", "6,6 - 7,6", "6,7 - 7,7", "7,3 - 7,4", "8,6 - 8,7"
    ]

    domain_conditions = []
    for i in range(1, 10):
        for j in range(1, 10):
            domain_conditions.append(f"(and (>= (A {i} {j}) 1) (<= (A {i} {j}) 9))")
    domain_assert = "(assert (and\n    " + "\n    ".join(domain_conditions) + "\n))"
    
    row_conditions = []
    for i in range(1, 10):
        row_cells = [f"(A {i} {j})" for j in range(1, 10)]
        row_conditions.append(f"(distinct {' '.join(row_cells)})")
    row_assert = "(assert (and\n    " + "\n    ".join(row_conditions) + "\n))"
    col_conditions = []
    for j in range(1, 10):
        col_cells = [f"(A {i} {j})" for i in range(1, 10)]
        col_conditions.append(f"(distinct {' '.join(col_cells)})")
    col_assert = "(assert (and\n    " + "\n    ".join(col_conditions) + "\n))"
    
    block_conditions = []
    for br in range(3):
        for bc in range(3):
            block_cells = []
            for i in range(3):
                for j in range(3):
                    row_index = 3 * br + i + 1
                    col_index = 3 * bc + j + 1
                    block_cells.append(f"(A {row_index} {col_index})")
            block_conditions.append(f"(distinct {' '.join(block_cells)})")
    block_assert = "(assert (and\n    " + "\n    ".join(block_conditions) + "\n))"
    
    # Process fixed constraints from embedded puzzle data
    fixed_constraints = []
    for i, line in enumerate(puzzle_data, start=1):
        entries = line.strip().split()
        for j, entry in enumerate(entries, start=1):
            if entry not in ['-', '.']:
                fixed_constraints.append(f"(assert (= (A {i} {j}) {entry}))")
    fixed_assert = "\n".join(fixed_constraints)
    
    # Process LQ constraints from embedded data
    lq_asserts = []
    for constraint in lq_constraints:
        if not constraint.strip():
            continue
        parts = constraint.split('-')
        if len(parts) != 2:
            continue
        left, right = parts[0].strip(), parts[1].strip()
        r1, c1 = left.split(',')
        r2, c2 = right.split(',')
        lq_asserts.append(f"(assert (< (A {r1} {c1}) (A {r2} {c2})))")
    lq_assert = "\n".join(lq_asserts)
    
    # Process consecutive constraints from embedded data
    consec_asserts = []
    for constraint in consecutive_constraints:
        if not constraint.strip():
            continue
        parts = constraint.split('-')
        if len(parts) != 2:
            continue
        left, right = parts[0].strip(), parts[1].strip()
        r1, c1 = left.split(',')
        r2, c2 = right.split(',')
        consec_asserts.append(
            f"(assert (or (= (- (A {r1} {c1}) (A {r2} {c2})) 1) (= (- (A {r2} {c2}) (A {r1} {c1})) 1)))"
        )
    consecutive_assert = "\n".join(consec_asserts)
    
    get_value_command = "(get-value (" + " ".join(f"(A {i} {j})" for i in range(1, 10) for j in range(1, 10)) + "))"
    
    smt2_content = f"""
; 9×9 Sudoku with additional inequality ('<') and consecutive ('o') constraints
(declare-fun A (Int Int) Int)

; Domain constraints
{domain_assert}

; Row constraints
{row_assert}

; Column constraints
{col_assert}

; Block constraints
{block_assert}

; Fixed cell constraints
{fixed_assert}

; LQ constraints (inequalities)
{lq_assert}

; Consecutive constraints
{consecutive_assert}

(check-sat)
{get_value_command}
(exit)
"""
    with open(smt2_filename, "w") as f:
        f.write(smt2_content.strip())
    
    print(f"SMT2 file '{smt2_filename}' has been generated.")

def visualize_sudoku_enhanced(grid):
    """Enhanced visualization with different styling and colors"""
    # Create figure with larger size and different styling
    fig, ax = plt.subplots(figsize=(8, 8))
    
    # Set background color
    fig.patch.set_facecolor('#f0f0f0')
    ax.set_facecolor('#ffffff')
    
    # Define colors for different 3x3 blocks
    block_colors = [
        '#e6f3ff', '#ffe6e6', '#e6ffe6',  # Top row blocks
        '#fff9e6', '#f0e6ff', '#ffe6f9',  # Middle row blocks
        '#e6fff9', '#f9ffe6', '#ffe6f0'   # Bottom row blocks
    ]
    
    # Add colored backgrounds for 3x3 blocks
    for block_row in range(3):
        for block_col in range(3):
            block_idx = block_row * 3 + block_col
            rect = Rectangle(
                (block_col * 3 - 0.45, block_row * 3 - 0.45),
                2.9, 2.9,
                facecolor=block_colors[block_idx],
                alpha=0.3,
                zorder=0
            )
            ax.add_patch(rect)
    
    # Set up grid with custom styling
    ax.set_xticks(np.arange(10) - 0.5)
    ax.set_yticks(np.arange(10) - 0.5)
    ax.set_xticklabels([])
    ax.set_yticklabels([])
    
    # Draw thick lines for 3x3 block boundaries
    for i in range(0, 10, 3):
        ax.axhline(i - 0.5, color='#2c3e50', linewidth=3, zorder=2)
        ax.axvline(i - 0.5, color='#2c3e50', linewidth=3, zorder=2)
    
    # Draw thin lines for individual cells
    for i in range(10):
        if i % 3 != 0:
            ax.axhline(i - 0.5, color='#7f8c8d', linewidth=1, alpha=0.7, zorder=1)
            ax.axvline(i - 0.5, color='#7f8c8d', linewidth=1, alpha=0.7, zorder=1)
    
    # Add numbers with enhanced styling
    for i in range(9):
        for j in range(9):
            if grid[i][j] != 0:
                # Use different colors and fonts for visual appeal
                text_color = '#2c3e50'
                font_weight = 'bold'
                font_size = 16
                
                # Add subtle shadow effect
                ax.text(j + 0.02, i + 0.02, str(grid[i][j]), 
                       va='center', ha='center', 
                       fontsize=font_size, 
                       color='#bdc3c7',
                       weight=font_weight,
                       zorder=2)
                
                # Main text
                ax.text(j, i, str(grid[i][j]), 
                       va='center', ha='center', 
                       fontsize=font_size, 
                       color=text_color,
                       weight=font_weight,
                       zorder=3)
    
    # Set limits and remove axes
    ax.set_xlim(-0.5, 8.5)
    ax.set_ylim(8.5, -0.5)
    ax.set_aspect('equal')
    
    # Add title with styling
    plt.title('Enhanced Sudoku Solution', 
              fontsize=18, 
              fontweight='bold', 
              color='#2c3e50',
              pad=20)
    
    # Remove axis spines for cleaner look
    for spine in ax.spines.values():
        spine.set_visible(False)
    
    # Save with higher DPI for better quality
    plt.savefig("sudoku_solution_enhanced.png", 
                dpi=300, 
                bbox_inches='tight', 
                facecolor='#f0f0f0',
                edgecolor='none')
    plt.close()
    print("Enhanced visualization saved as 'sudoku_solution_enhanced.png'")

def run_z3_and_visualize(filename):
    try:
        result = subprocess.run(["z3", filename], capture_output=True, text=True, timeout=30)
        output = result.stdout.strip()
        error_output = result.stderr.strip()
        
        print(f"Z3 stdout: {output}")
        if error_output:
            print(f"Z3 stderr: {error_output}")
        
    except subprocess.TimeoutExpired:
        print("Z3 timed out after 30 seconds.")
        return
    except FileNotFoundError:
        print("Error: Z3 is not installed or not found in PATH.")
        return
    except Exception as e:
        print(f"Error running Z3: {e}")
        return
    
    if "unsat" in output.lower():
        print("Z3 says the problem is unsatisfiable.")
        return
    elif "sat" not in output.lower():
        print("Z3 did not return 'sat'—something is unusual.")
        print(f"Full output: {output}")
        return
    
    pattern = re.compile(r'\(A\s+(\d+)\s+(\d+)\)\s+(\d+)')
    matches = pattern.findall(output)
    
    model_dict = {}
    for match in matches:
        i, j, val = map(int, match)
        model_dict[(i, j)] = val
    
    grid = []
    for i in range(1, 10):
        row = []
        for j in range(1, 10):
            row.append(model_dict.get((i, j), 0))
        grid.append(row)
    
    # Use the enhanced visualization function
    visualize_sudoku_enhanced(grid)

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Enhanced Sudoku SMT2 Generator and Solver with extra constraints")
    parser.add_argument("--smt2", type=str, default="1.smt2", help="Output SMT2 filename")
    args = parser.parse_args()
    
    generate_smt2(args.smt2)
    run_z3_and_visualize(args.smt2)
