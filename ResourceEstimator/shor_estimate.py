import math
import copy
import csv

# Represents the costs of something with circuits
# optimizing for low width, low depth, etc.
class Cost:
	def __init__(self, low_depth, low_T, low_width):
		self.low_depth = low_depth
		self.low_T = low_T
		self.low_width = low_width

	def add(self, cost2):
		return Cost(
			low_depth = self.low_depth.add(cost2.low_depth), 
			low_T = self.low_T.add(cost2.low_T),
			low_width = self.low_width.add(cost2.low_width)
		)

	def subtract(self, cost2):
		return Cost(
			low_depth = self.low_depth.subtract(cost2.low_depth), 
			low_T = self.low_T.subtract(cost2.low_T),
			low_width = self.low_width.subtract(cost2.low_width)
		)
	def multiply(self, n):
		return Cost(
			low_depth = self.low_depth.multiply(n), 
			low_T = self.low_T.multiply(n),
			low_width = self.low_width.multiply(n)
		)
	def message(self):
		 message = ""
		 message += "Width-optimal: \n" +self.low_width.message()
		 message += "T-optimal: \n" + self.low_T.message()
		 message += "Depth-optimal: \n" + self.low_depth.message() + "\n"
		 return message


# Contains all relevant cost metrics for a single circuit
class SingleCost:
	def __init__(self, width, T_depth, full_depth, measure, T_count, single_qubit, CNOT):
		self.width = width
		self.T_depth = T_depth
		self.T_count = T_count
		self.full_depth = full_depth
		self.measure = measure
		self.single_qubit = single_qubit
		self.CNOT = CNOT

	# Costs of two sequential circuits
	# Uses the maximum width (assumes circuits are run sequentially)
	def add(self, cost2):
		return SingleCost(
			width = max(self.width, cost2.width),
			T_depth = self.T_depth + cost2.T_depth,
			T_count = self.T_count + cost2.T_count,
			full_depth = self.full_depth + cost2.full_depth,
			measure = self.measure + cost2.measure,
			single_qubit = self.single_qubit + cost2.single_qubit,
			CNOT = self.CNOT + cost2.CNOT,
		)

	# Subtracts
	# Assumes the width actually stays the same (does not decrease!)
	def subtract(self, cost2):
		return SingleCost(
			width = self.width,
			T_depth = self.T_depth - cost2.T_depth,
			T_count = self.T_count - cost2.T_count,
			full_depth = self.full_depth - cost2.full_depth,
			measure = self.measure - cost2.measure,
			single_qubit = self.single_qubit - cost2.single_qubit,
			CNOT = self.CNOT - cost2.CNOT,
		)
	def multiply(self, n):
		return SingleCost(
			width = self.width,
			T_depth = self.T_depth * n,
			T_count = self.T_count * n,
			full_depth = self.full_depth * n,
			measure = self.measure * n,
			single_qubit = self.single_qubit * n,
			CNOT = self.CNOT * n
		)
	#Outputs the costs to a string
	def message(self):
		message = ""
		message += "    CNOT: " + str(self.CNOT) + "\n"
		message += "    Single-qubit: " + str(self.single_qubit) + "\n"
		message += "    Measurements: " + str(self.measure) + "\n"
		message += "    T gates: " + str(self.T_count) + "\n"
		message += "    T-depth: " + str(self.T_depth) + "\n"
		message += "    Full depth: " + str(self.full_depth) + "\n"
		message += "    Width: " +str( self.width) + "\n"
		return message

	#A string which can act as a header for a similar csv as Q# outputs
	@classmethod
	def CSV_header(Class):
		return "CNOT, Single Qubit, T gates, R gates, Measurements, T-depth, Initial Width, Extra Width, Full Depth, Window Size, Size\n"

	# Outputs the costs in a row that matches the header
	def csv_row(self):
		message = ""
		message += str(self.CNOT) + ", "
		message += str(self.single_qubit) + ", "
		message += str(self.T_count) + ", ,"
		message += str(self.measure) + ", "
		message += str(self.T_depth) + ", ,"
		message += str(self.width) + ","
		message += str(self.full_depth)
		return message

# Returns the cost of a lookup for an n-bit elliptic curve point 
# among a table of 2^window_size points
# Extrapolations based on output of Q#
def Lookup_Cost(n, window_size):
	main_exponent = 2**window_size;
	costs = Cost(
		low_T = SingleCost(
			width = 2.678*window_size + 19.81+2.01*n,
			T_depth = 0.50733*main_exponent+23.0,
			full_depth = 17.04 * main_exponent + 101.04,
			measure = 1.503*main_exponent + 4.071 + 2.0*n,
			T_count = 4.0*main_exponent + 24.0,
			single_qubit = 7.74 * main_exponent + 10.68 + 2.0*n,
			CNOT = 115.13 * main_exponent + 117.76
		),
		low_width = SingleCost(
			width = 2.657*window_size + 21.623 + 2.0*n,
			T_depth = 0.50733*main_exponent + 23.0,
			full_depth = 16.96 * main_exponent + 97.98,
			measure = 1.516*main_exponent + 2.288 + 2.0*n,
			T_count = 4.0*main_exponent + 24.0,
			single_qubit = 7.793 * main_exponent + 5.75 + 2.0*n,
			CNOT = main_exponent*(110.73+0.016*n) + 136.793
		),
		low_depth = SingleCost(
			width = 2.657*window_size + 21.623 + 2.0*n,
			T_depth = 0.50733*main_exponent + 23.0,
			full_depth = 16.96 * main_exponent + 97.63,
			measure = 1.516 * main_exponent + 2.185+2.0*n,
			T_count = 4.0*main_exponent+24.0,
			single_qubit = 7.793*main_exponent + 5.218 + 2.0*n,
			CNOT = main_exponent*(110.74 + 0.016 * n) + 134.52
		)
	)	
	return costs

# Returns the costs of a single point addition with 
# window size of 8
# Based on estimates from Q#
def point_addition_cost(n):
	costs = {}
	nsquared = n*n
	lgn = math.log(n)/math.log(2.0)
	nlgn = n*lgn
	n2lgn = nsquared*lgn
	costs = Cost(
		low_T = SingleCost(
			width = 10.0*n + 1.5*math.floor(lgn) + 18.9,
			T_depth = 431.6*nsquared + 17572,
			full_depth = 1562 * nsquared + 120830,
			measure = 85*nsquared + 19465,
			T_count = 1182*nsquared + 92166,
			single_qubit = 648*nsquared + 101890,
			CNOT = 2391*nsquared + 473340
		),
		low_width = SingleCost(
			width = 7.99*n + 3.81*math.floor(lgn) + 17.1,
			T_depth = 144.5 * n2lgn + 626302,
			full_depth = 464.6 * n2lgn + 2074976,
			measure = 753.7*n2lgn - 21095,
			T_count = 503.4*n2lgn + 1318387,
			single_qubit = 167.7 * n2lgn + 544865,
			CNOT = 751.2*n2lgn + 2296571
		),
		low_depth = SingleCost(
			width = 11.0*n + 28.6,
			T_depth = 226.1*nlgn + 14469,
			full_depth = 1485*nlgn + 52413,
			measure = 202.5*nsquared - 14509,
			T_count = 2745*nsquared - 85878,
			single_qubit = 1462*nsquared - 35830,
			CNOT = 6481*nsquared+44882
		)
	)	

	return costs

def load_from_csv(csv_file_name, n, existing_costs = None):
	csv.register_dialect('cost_csv_dialect', skipinitialspace = True)
	with open(csv_file_name, newline="\n") as csvfile:
		csvCosts = csv.DictReader(csvfile, dialect='cost_csv_dialect')
		costs = SingleCost(0,0,0,0,0,0,0)
		for row in csvCosts:
			if (row['size'] == str(n)):
				if existing_costs is None:
					costs.CNOT = int(row['CNOT count'])
					costs.single_qubit = int(row['1-qubit Clifford count'])
					costs.T_count = int(row['T count'])
					costs.measure = int(row['M count'])
					costs.T_depth = int(row['T depth'])
					costs.width = int(row['extra width'])
					print(costs)
				else:
					costs = existing_costs
					costs.full_depth = int(row['Full depth'])
	return costs

# Returns the costs of a single point addition with 
# window size of 8 for fixed-modulus curves
# Based on estimates from Q#
def fixed_modulus_point_addition_cost(n):
	low_T_costs = load_from_csv('EllipticCurveEstimates/LowT/Fixed-modulus-signed.csv', n)
	low_T_costs = load_from_csv('EllipticCurveEstimates/LowT/Fixed-modulus-signed-all-gates.csv', n, low_T_costs)

	low_width_costs = load_from_csv('EllipticCurveEstimates/LowWidth/Fixed-modulus-signed.csv', n)
	low_width_costs = load_from_csv('EllipticCurveEstimates/LowWidth/Fixed-modulus-signed-all-gates.csv', n, low_width_costs)

	low_depth_costs = load_from_csv('EllipticCurveEstimates/LowDepth/Fixed-modulus-signed.csv', n)
	low_depth_costs = load_from_csv('EllipticCurveEstimates/LowDepth/Fixed-modulus-signed-all-gates.csv', n, low_depth_costs)

	return Cost(low_T = low_T_costs, low_width = low_width_costs, low_depth = low_depth_costs)

	# Earlier code based on original estimates

	# if (n==256):
	# 	costs = Cost(
	# 		low_T = SingleCost(
	# 			CNOT = 178374765,
	# 			single_qubit = 178374765,
	# 			T_count = 77857742,
	# 			measure = 5656061,
	# 			T_depth = 28341737,
	# 			width = 2589,
	# 			full_depth = 102860240
	# 		),
	# 		low_width = SingleCost(
	# 			CNOT = 462602294,
	# 			single_qubit = 94262398,
	# 			T_count = 272662642,
	# 			measure = 138293,
	# 			T_depth = 90582946,
	# 			width = 2091,
	# 			full_depth = 296669779
	# 		),
	# 		low_depth = SingleCost(
	# 			CNOT = 436193618,
	# 			single_qubit = 96254895,
	# 			T_count = 179587682,
	# 			measure = 13210138,
	# 			T_depth = 490199,
	# 			width = 2852,
	# 			full_depth = 3174193
	# 		)
	# 	)
	# elif (n==384):
	# 	costs = Cost(
	# 		low_T = SingleCost(
	# 			CNOT = 430987821,	
	# 			single_qubit = 95880884,
	# 			T_count = 174518574,
	# 			measure = 12587943,
	# 			T_depth = 63680030,
	# 			width = 3869,
	# 			full_depth = 230756452
	# 		),
	# 		low_width = SingleCost(
	# 			CNOT = 1159548116,
	# 			single_qubit = 236838325,
	# 			T_count = 673208736,
	# 			measure = 207807,
	# 			T_depth = 220807469,
	# 			width = 3115,
	# 			full_depth = 728740733
	# 		),
	# 		low_depth = SingleCost(
	# 			CNOT = 999485914,
	# 			single_qubit = 217697269,
	# 			T_count = 404345120,
	# 			measure = 29787028,
	# 			T_depth = 758770,
	# 			width = 4259,
	# 			full_depth = 4989451
	# 		)
	# 	)
	# elif (n==521):
	# 	costs = Cost(
	# 		low_T = SingleCost(
	# 			CNOT = 822773626,
	# 			single_qubit = 175844612,
	# 			T_count = 320708573,
	# 			measure = 23051575,
	# 			T_depth = 117140503,
	# 			width = 5240,
	# 			full_depth = 424156807
	# 		),
	# 		low_width = SingleCost(
	# 			CNOT = 2263078766,
	# 			single_qubit = 448325541,
	# 			T_count = 1260252894,
	# 			measure = 497700,
	# 			T_depth = 412301349,
	# 			width = 4215,
	# 			full_depth = 1382063806
	# 		),
	# 		low_depth = SingleCost(
	# 			CNOT = 1860934280,
	# 			single_qubit = 402483115,
	# 			T_count = 745693019,
	# 			measure = 55016018,
	# 			T_depth = 1057516,
	# 			width = 5770,
	# 			full_depth  = 7135001
	# 		)
	# 	)
	# else:
	# 	raise InputError("No data for fixed modulus of size" + str(n))
	# return costs


def get_optimal_shor(addition_cost, n):
	#addition_cost = point_addition_cost(n)
	eight_lookup_cost = Lookup_Cost(n, 8).multiply(6)
	# The cost of an addition without any lookups
	# We also want to remove the qubits, too
	blank_addition_cost = addition_cost.subtract(eight_lookup_cost)
	blank_addition_cost.low_depth.width -= eight_lookup_cost.low_depth.width
	blank_addition_cost.low_T.width -= eight_lookup_cost.low_T.width
	blank_addition_cost.low_width.width -= eight_lookup_cost.low_width.width
	best_T_size = 8
	best_T = addition_cost.multiply(2*n)
	best_depth = addition_cost.multiply(2*n)
	best_depth_size = 8
	best_width = addition_cost.multiply(2*n)
	best_width_size = 8
	# Check all window sizes up to n/2
	for i in range(int(n/2)):
		# number of windows
		num_windows = math.floor( n / (i+1))
		# size of remainder window
		remainder_window = max(n - num_windows * (i+1), 0)
		main_lookup_costs = Lookup_Cost(n,i).multiply(6)
		# Add in the cost of doing that many lookups
		main_addition_cost = blank_addition_cost.add(main_lookup_costs)
		# The number of point additions that need to be done
		total_cost = main_addition_cost.multiply(2*num_windows)
		
		# If there is a "remainder window" (a window smaller than the 
		# others to finish the remaining bits), add that cost
		if remainder_window > 0:
			second_lookup_costs = Lookup_Cost(n,remainder_window).multiply(6)
			second_addition_cost = blank_addition_cost.add(second_lookup_costs)
			total_cost = total_cost.add(second_addition_cost.multiply(2))
			#Here we add whichever width is greater
			total_cost.low_depth.width += max(second_lookup_costs.low_depth.width, main_lookup_costs.low_depth.width)
			total_cost.low_T.width += max(second_lookup_costs.low_T.width, main_lookup_costs.low_T.width)
			total_cost.low_width.width += max(second_lookup_costs.low_width.width, main_lookup_costs.low_width.width)
		else:
			#With no remainder window, we add just the main lookup width
			total_cost.low_depth.width += main_lookup_costs.low_depth.width
			total_cost.low_T.width += main_lookup_costs.low_T.width
			total_cost.low_width.width += main_lookup_costs.low_width.width
		# Compare to previous best counts, update as needed
		if total_cost.low_T.T_count < best_T.low_T.T_count:	
			best_T = copy.deepcopy(total_cost)
			best_T_size = i
		if total_cost.low_width.T_count < best_width.low_width.T_count:
			best_width = copy.deepcopy(total_cost)
			best_width_size = i
		if total_cost.low_depth.T_depth < best_depth.low_depth.T_depth:
			best_depth = copy.deepcopy(total_cost)
			best_depth_size = i

	return {"T": best_T, "depth": best_depth, "width" : best_width, "T-window" : best_T_size, "depth-window" : best_depth_size, "width-window" : best_width_size}


# Checks all elliptic curve sizes up to 521, writes to csv files
T_CSV = SingleCost.CSV_header()
depth_CSV = SingleCost.CSV_header()
width_CSV = SingleCost.CSV_header()
for i in range(10,522):
	costs = get_optimal_shor(point_addition_cost(i), i)
	T_CSV += costs["T"].low_T.csv_row() + "," + str(costs["T-window"]) + "," + str(i) + "\n"
	depth_CSV += costs["depth"].low_depth.csv_row() + "," + str(costs["depth-window"]) + "," + str(i) + "\n"
	width_CSV += costs["width"].low_width.csv_row() + "," + str(costs["width-window"]) + "," + str(i) + "\n"




t_file = open('shor_low_t.csv', 'a')
t_file.write(T_CSV)
t_file.close()

depth_file = open('shor_low_depth.csv', 'a')
depth_file.write(depth_CSV)
depth_file.close()

width_file = open('shor_low_width.csv', 'a')
width_file.write(width_CSV)
width_file.close()

# Check fixed modulus sizes
T_CSV = SingleCost.CSV_header()
depth_CSV = SingleCost.CSV_header()
width_CSV = SingleCost.CSV_header()
for i in {256, 384, 521}:
	costs = get_optimal_shor(fixed_modulus_point_addition_cost(i), i)
	T_CSV += costs["T"].low_T.csv_row() + "," + str(costs["T-window"]) + "," + str(i) + "\n"
	depth_CSV += costs["depth"].low_depth.csv_row() + "," + str(costs["depth-window"]) + "," + str(i) + "\n"
	width_CSV += costs["width"].low_width.csv_row() + "," + str(costs["width-window"]) + "," + str(i) + "\n"


t_file = open('shor_low_t_fixed.csv', 'a')
t_file.write(T_CSV)
t_file.close()

depth_file = open('shor_low_depth_fixed.csv', 'a')
depth_file.write(depth_CSV)
depth_file.close()

width_file = open('shor_low_width_fixed.csv', 'a')
width_file.write(width_CSV)
width_file.close()
