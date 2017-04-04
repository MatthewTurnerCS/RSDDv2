/*  FuzzSMT: Fuzzing tool for Satisfiablity Modulo Theories (SMT) benchmarks.
 *  Copyright (C) 2009  Robert Daniel Brummayer
 *
 *  This file is an extension of FuzzSMT by Sam Olds and Matthew Turner.
 *  Added 2017
 *
 *  FuzzSMT is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  FuzzSMT is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

public class FloatType extends SMTType {

	protected String name;

	protected int bits;  

	public FloatType(int b) {	  
		assert(b > 0);
		this.bits = b;
		this.name = "Float" + b;
	}

	public String toString() {
		return this.name;
	}

	public int getWidth(){
		return this.bits;
	}

	public boolean equals (Object o){
		assert (o != null);

		if (! (o instanceof FloatType))
			return false;

		return this.bits == ((FloatType) o).bits;
	}

}