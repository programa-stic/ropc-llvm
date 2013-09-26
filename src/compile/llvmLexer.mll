(* Header section *)
{
	open Lexing

	open LlvmParser

	let create_hashtable size init =
		let tbl = Hashtbl.create size in
		List.iter (fun (key, data) -> Hashtbl.add tbl key data) init;
		tbl

    let keyword_table =
	create_hashtable 32 [
		(* Bitwise Binary Operations *)
		("and", AND);

		(* Binary Operations *)
		("add", ADD);
		("sub", SUB);
        ("mul", MUL);

		(* Conversion Operations *)
		("bitcast", BITCAST);

		(* Terminator Instructions *)
		("ret", RET);
		("br", BR);

		(* Memory Access and Addressing Operations *)
		("alloca", ALLOCA);
		("store", STORE);
		("load", LOAD);
		("getelementptr", GETELEMENTPTR);

		(* Other Instructions *)
		("icmp", ICMP);
		("call", CALL);
		("define", FUN);
		("declare", DECLARE);

		(* Miscellaneous *)
		("label", LABEL);
		("align", ALIGN);
		("to", TO);
		("inbounds", INBOUNDS);

		(* Function Attributes *)
		("nounwind", NOUNWIND);
		("uwtable", UWTABLE);

		(* Parameter Attributes *)
		("nocapture", NOCAPTURE);

		(* Target Information *)
		("target", TARGET);

		(* Global Variables *)
		("private", PRIVATE);
		("unnamed_addr", UNNAMED_ADDR);
		("constant", CONSTANT);
	]

    let incr_linenum lexbuf =
        let pos = lexbuf.lex_curr_p in
        lexbuf.lex_curr_p <- { pos with
          pos_lnum = pos.pos_lnum + 1;
          pos_bol = pos.pos_cnum;
        }

    let unpack_c_str c_str =
        let _ = Str.string_match (Str.regexp "c\"\\(.*\\)\"") c_str 0 in
            Str.matched_group 1 c_str
}

(* Definitions section *)
let ellipsis = "..."
let boolean = "true" | "false"
let digit = ['0'-'9']
let br_cond = "eq" | "ne" | "ugt" | "uge" | "ult" | "ule" | "sgt" | "sge" | "slt" | "sle"
let op_sign = "nsw" | "nuw"
let id = ['%''@']['a'-'z' 'A'-'Z' '0'-'9']['a'-'z'  'A'-'Z' '0'-'9' '_' '.']*
let keyword = ['a'-'z' 'A'-'Z']['a'-'z'  'A'-'Z' '0'-'9' '_']*
let str = '"' [^'"']* '"'
let str2 = '\'' [^'\'']* '\''
let cstr = 'c' '"' [^'"']* '"'

(* Rules section *)
rule token = parse

	(* Array Type *)
	| '[' digit+ " x " keyword ']' '*'* as ty
	{
		Printf.printf "TYPE: %s\n" ty;
		TYPE ty
	}

	(* Boolean *)
	| "true" | "false" as vbul
	{
		let bul = bool_of_string vbul in
		Printf.printf "bool: %s (%B)\n" vbul bul;
		BOOL bul
	}

	(* Numbers *)
	| digit+ as inum
	{
		let num = int_of_string inum in
		Printf.printf "integer: %s (%d)\n" inum num;
		NUM num
	}

	(* Strings *)
	| cstr as s
	{
		CSTR (unpack_c_str s)
	}

	(* Strings *)
	| str as s
	{
		STR s
	}

	(* Ellipsis *)
    | ellipsis
    {
		ELLIPSIS
    }

	(* Branch condition *)
    | br_cond as cond
    {
		COND cond
    }

    (* Operation signedness *)
    | op_sign as sign
    {
		SIGN sign
    }

    (* Label target *)
    | "; <label>:"
    {
    	LABEL_TARGET
    }

    (* Ignore ModuleID *)
    | "; ModuleID = " str2 as moduleID
    {
    	Printf.printf "moduleID: %s\n" moduleID;
    	token lexbuf
    }

    (* Ignore preds *)
    | "; preds = " (id | ", ")* as preds
    {
    	Printf.printf "preds: %s\n" preds;
    	token lexbuf
    }

    (* Gobal and local identifiers *)
	| id as identifier
    {
    	Printf.printf "identifier: %s\n" identifier;
		ID identifier
    }

	| keyword '*'* as identifier
    {
		try
			let token = Hashtbl.find keyword_table identifier in
			Printf.printf "keyword: %s\n" identifier;
			token
		with Not_found ->
			if String.compare identifier "false" == 0 then
				begin
				Printf.printf "identifier: %s\n" identifier;
				ID identifier
				end
			else
				begin
				Printf.printf "type: %s\n" identifier;
				TYPE identifier
				end
    }

    (* Misc. characters *)
	| '='					{ EQ }
	| ','					{ COMMA }
	| '('					{ LPAREN }
	| ')'					{ RPAREN }
	| '{'					{ LCURLY }
	| '}'					{ RCURLY }

	(* Consume whitespace *)
    | [' ' '\t']
    {
        token lexbuf
    }

	(* Consume one-line comments *)
    | '#' [^'\n']*
    {
        token lexbuf
    }

	(* Consume newlines *)
    | ['\n']
    {
		incr_linenum lexbuf;
		token lexbuf
    }

	(* Unknown characters *)
    | _ as c
    {
		Printf.printf "Unrecognized character: %c\n" c;
		token lexbuf
    }

    (* End of file *)
	| eof					{ EOF }


(* Trailer section *)