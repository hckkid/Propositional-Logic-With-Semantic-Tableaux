use "Form.sml";
signature SEMANTICTABLEAUX = sig
	datatype tableaux = tableauxAbs | tableaux1 of Form.form | tableaux2 of Form.form*tableaux | tableaux3 of Form.form*tableaux*tableaux
	exception InvalidInput
	val generateTableaux : Form.form -> tableaux
	(* val isValid : Form.form -> bool *)
	(* val isSatisfiable : Form.form -> bool *)
	(* val isContradiction : Form.form -> bool *)
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
end;