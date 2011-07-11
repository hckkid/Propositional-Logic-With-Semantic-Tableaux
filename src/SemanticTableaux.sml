use "Form.sml";
signature SEMANTICTABLEAUX = sig
	datatype tableaux = tableauxAbs | tableaux1 of Form.form | tableaux2 of Form.form*tableaux | tableaux3 of Form.form*tableaux*tableaux
	exception InvalidInput
	val generateTableaux : Form.form -> tableaux
	val isValid : Form.form -> bool
	val isSatisfiable : Form.form -> bool
	val isContradiction : Form.form -> bool
end
structure SemanticTableaux :> SEMANTICTABLEAUX = struct
	datatype tableaux = tableauxAbs | tableaux1 of Form.form | tableaux2 of Form.form*tableaux | tableaux3 of Form.form*tableaux*tableaux
	exception InvalidInput
	fun generateTableaux(f) = 
		let
			fun tmpGenerateTableaux([Form.Absurdum]) = tableauxAbs
				| tmpGenerateTableaux([Form.propSymb P]) = (tableaux1 (Form.propSymb P))
				| tmpGenerateTableaux([Form.Negation(Form.propSymb P)]) = (tableaux1 (Form.Negation(Form.propSymb P)))
				| tmpGenerateTableaux([Form.Negation(Form.Absurdum)]) = (tableaux1 (Form.Negation(Form.Absurdum)))
				| tmpGenerateTableaux(Form.Conjunction(A,B)::xs) = tableaux2 (Form.Conjunction(A,B),tmpGenerateTableaux([A,B] @ xs))
				| tmpGenerateTableaux(Form.Disjunction(A,B)::xs) = tableaux3 (Form.Disjunction(A,B),tmpGenerateTableaux(A::xs),tmpGenerateTableaux(B::xs))
				| tmpGenerateTableaux(Form.Implication(A,B)::xs) = tableaux2 (Form.Implication(A,B),tmpGenerateTableaux(Form.Disjunction(Form.Negation(A),B)::xs))
				| tmpGenerateTableaux(Form.Negation(Form.Conjunction(A,B))::xs) = tableaux2 (Form.Negation(Form.Conjunction(A,B)),tmpGenerateTableaux(Form.Disjunction(Form.Negation(A),Form.Negation(B))::xs))
				| tmpGenerateTableaux(Form.Negation(Form.Disjunction(A,B))::xs) = tableaux2 (Form.Negation(Form.Disjunction(A,B)),tmpGenerateTableaux(Form.Conjunction(Form.Negation(A),Form.Negation(B))::xs))
				| tmpGenerateTableaux(Form.Negation(Form.Implication(A,B))::xs) = tableaux2 (Form.Negation(Form.Implication(A,B)),tmpGenerateTableaux(Form.Conjunction(A,Form.Negation(B))::xs))
				| tmpGenerateTableaux(Form.Negation(Form.Negation(A))::xs) = tableaux2 (Form.Negation(Form.Negation(A)),tmpGenerateTableaux(A::xs))
				| tmpGenerateTableaux(f::xs) = (tableaux2 (f,tmpGenerateTableaux(xs)))
				| tmpGenerateTableaux([]) = raise InvalidInput
		in tmpGenerateTableaux([f])
		end
		handle InvalidInput => raise InvalidInput
	fun isEveryNodeClosed(tableauxAbs,_) = true
		| isEveryNodeClosed(tableaux1(Form.Negation(Form.Absurdum)),_) = false
		| isEveryNodeClosed(tableaux1(Form.propSymb(x)),[]) = false
		| isEveryNodeClosed(tableaux1(Form.propSymb(x)),y::ys) = if (y = Form.Negation(Form.propSymb(x))) then true else isEveryNodeClosed(tableaux1(Form.propSymb(x)),ys)
		| isEveryNodeClosed(tableaux1(Form.Negation(Form.propSymb(x))),[]) = false
		| isEveryNodeClosed(tableaux1(Form.Negation(Form.propSymb(x))),y::ys) = if (y = Form.propSymb(x)) then true else isEveryNodeClosed(tableaux1(Form.Negation(Form.propSymb(x))),ys)
		| isEveryNodeClosed(tableaux2(Form.propSymb(x),y),z) = isEveryNodeClosed(y,Form.propSymb(x)::z)
		| isEveryNodeClosed(tableaux2(Form.Negation(Form.propSymb(x)),y),z) = isEveryNodeClosed(y,Form.Negation(Form.propSymb(x))::z)
		| isEveryNodeClosed(tableaux2(Form.Absurdum,y),_) = true
		| isEveryNodeClosed(tableaux2(Form.Negation(Form.Absurdum),y),z) = isEveryNodeClosed(y,z)
		| isEveryNodeClosed(tableaux2(_,x),z) = isEveryNodeClosed(x,z)
		| isEveryNodeClosed(tableaux3(_,x,y),z) = (isEveryNodeClosed(x,z) andalso isEveryNodeClosed(x,z))
	fun isContradiction(f) = isEveryNodeClosed(generateTableaux(f),[])
	fun isValid(f) = isContradiction(Form.Negation(f))
	fun isSatisfiable(f) = not(isContradiction(f))
end;