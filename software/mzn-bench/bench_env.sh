if [[ "${BASH_SOURCE[0]}" = "${0}" ]]; then
	    >&2 echo "Remember: you need to run me as 'source bench_env.sh', not execute it!"
	        exit
fi

# Create or activate Python virtual environment
if [ -d venv ]; then
	    source venv/bin/activate
    else
	    python3 -m venv venv
	    source venv/bin/activate
	    python3 -m pip install python-sat pytest-html pytest minizinc
	    python3 -m pip install -e ../minizinc-python
	    python3 -m pip install -e .[scripts,plotting]
fi

# Set other environment variables and load cluster modules
if [[ $(hostname) != 'air' ]]; then
  module load Gecode Gurobi Chuffed CoinUtils GMP 
fi


