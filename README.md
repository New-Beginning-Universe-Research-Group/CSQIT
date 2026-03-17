# CSQIT (Cosmological Quantum Information Theory)
## Version 10.4.5 (March 17, 2026)

### English Description
This repository contains the complete formalization of CSQIT 10.4.5, a unified framework for quantum mechanics and general relativity based on nine axioms.

### 中文描述
本仓库包含 CSQIT 10.4.5 的完整形式化实现，这是一个基于九条公理、统一量子力学与广义相对论的理论框架。

## Repository Structure
CSQIT/
├── CSQIT/ # Core Lean definitions
├── Appendices/ # Complete formal proofs
│ ├── AppendixA/ # Operad uniqueness and associativity
│ ├── AppendixB/ # Causal structure and weaving
│ └── AppendixC/ # Global consistency and Regge calculus
├── simulations/ # Numerical verification code
└── [root files] # Configuration and metadata

##

## Version Information
- **Current Version**: 10.4.5
- **Release Date**: 2026-03-14
- **DOI**: 10.5281/zenodo.XXXXXXX (to be assigned)

## Quick Start
```bash
# Clone the repository
git clone https://github.com/New-Beginning-Universe-Research-Group/CSQIT.git
cd CSQIT

# Install Lean and Mathlib
lake exe cache get
lake build

# Run numerical simulations
pip install -r requirements.txt
python simulations/operad_spectrum.py

## Citation
If you use this code in your research, please cite:

Zhang, J. (2026). CSQIT 10.4.5: Complete Spacetime Quantum Information Theory.
Zenodo. DOI: 10.5281/zenodo.XXXXXXX

## License
MIT License - see LICENSE file for details.