{'V[Main:loan]': 'Int', 'V[Main:term]': 'Int'}

{'Main:loan_<_1000': ('(Main:loan) < (1000)', [('False', 'Main:loan_in_[1000,100000]'), ('True', 'Main:Low_-_Volume_loan')]), 
 
 'Main:Low_-_Volume_loan': ('None', [('True', 'Main:term_in_years_<_5')]),

 'Main:loan_in_[1000,100000]': ('And(((Main:loan) >= (1000)),((Main:loan) < (100000)))', [('False', 'Main:High_-_Volume_loan'), ('True', 'Main:Mid_-_Volume_loan')]), 
 
 'Main:Mid_-_Volume_loan': ('None', [('True', 'Main:term_in_years_<_5')]), 
 
 
 'Main:High_-_Volume_loan': ('None', [('True', 'Main:term_in_years_<_5')]),

 'Main:term_in_years_<_5': ('(Main:term) < (5)', [('False', 'Main:Long_term'), ('True', 'Main:Short_-_Term')]), 'Main:Short_-_Term': ('None', [('True', 'Main:Output_rate_')]),

 'Main:Long_term': ('None', [('True', 'Main:Output_rate_')]), 
 
 'Main:sinkT': ('Main:True', []), 
 
 'Main:sinkF': ('Main:True', [])}