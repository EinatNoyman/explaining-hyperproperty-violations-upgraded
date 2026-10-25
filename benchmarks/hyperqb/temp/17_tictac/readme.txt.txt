This is a compilation of all deliverables barring the final report which will be sent to you and Dr. Bonakdarpour later this week.

If I had more time I would have written a shorter letter - Ghandi

Changes
	*Added successful model for the noninterference case study.
	*Added a new noninterference hyper property to actually represent noninterference.
	*Switched out document for bank3 case study counter example. 
	*Recorded more outputs for the models
	*Added the final report

======================================================================================================================
Bank3:
	* bank3_fail_simple.smv : First version with minimal variables
	* bank3_fail_complex V1-V3 : Versions with additional variables / transitions, progressively more simple as these were initially written under the assumption that the model was too big and not that I had no idea what I was doing.
	* NEW: bank3_success_simple : loginfo now only records when the attempt is complete, and does not indicate the result of the attempt. 
	* dstore_noninf.hq : Non-inference Hyper property (forall forall, single-model), log_info leaks information about the state of the program unless its the same regardless of login success/failure.
	bank3_fail_simple_Counterexample: An excel file that organizes the counterexample outputted by HyperQB when ran on the simple bank model.
	* NEW : Noninterference.hq: Noninterference Hyper Property actually, (forall, forall, exists, single-modal) represents the in-class definition

	* MODIFIED: bank3_fail_simple_Counterexample.xlsx : Hyperqb output for the simple failure model that does not satisfy noninference, organized to show variable states at each point in time. Changed to new template.
======================================================================================================================

Constructor (Linearizability):

These models abstract concurrency using program counter variables for each "Process" (Constructor and Listener) a line of code is represented by everything that happens for a given value of the program counter variable of that process. Additionally to add a non-deterministic sequence of execution each PC requires its corresponding clock to be at zero to execute, this could have been done far easier by just allowing the PC to either tick or not but inefficiency is what makes something beautiful. 

	* constructor_sequential: Baseline model with no concurrency (Clocks can be set to zero to catch up to concurrent models)
	* constructor_atomic: Model with concurrency that does not allow reading until the constructor is finished (satisfies linearizability)
	constructor_conc: Model with concurrency that allows reading (does not satisfy linearizability.


	* MODIFIED : linearizable.hq: Linearizability Hyperproperty (forall, exists, duel-model) A represents the model to be tested and B represents the sequential model compares if there exists an output of the sequential model whoose output behaves like the execution of the model to be tested for any given execution.
	* test.hq: sanity check

	* Councurrent_Counterexample.xlsx : Hyperqb output for the concurrent model that does not satisfy linearizability, organized to show variable states at each point in time.
======================================================================================================================

Tictac:
	* tictac_modes.smv : The original tictac with a deterministic v. non-deterministic player or two non-deterministic players depending on the mode.
	* tictac.smv : A version that only uses the player vs computer mode (as player v player has 128k reachable states to this one's 597), and with some other syntactic changes to make it compatible with HyperQB
======================================================================================================================

	* Outputs.xls: Includes our outputs for each model and the command parameters used for it, as well as runtime/hardware information.
	* CSC814 Final Report.docx : The final report, not actually that useful but its here

