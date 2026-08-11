param(
    [ValidateRange(30, 3600)]
    [int]$TimeoutSeconds = 600,

    [string]$RunId = (Get-Date).ToUniversalTime().ToString('yyyyMMddTHHmmssZ'),

    [switch]$CentralOnly,

    [ValidateSet(
        'EAL6_FreeRTOS_V611_List_Smoke',
        'EAL6_FreeRTOS_V611_Model',
        'EAL6_FreeRTOS_V611_Scheduler_Abstract_Model',
        'EAL6_FreeRTOS_V611_M0_Bridge',
        'EAL6_FreeRTOS_V611_List_Raw_Skip',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Ordered_Probe',
        'EAL6_FreeRTOS_V611_List_Raw_R0_Guards',
        'EAL6_FreeRTOS_V611_List_Raw_R1_Init',
        'EAL6_FreeRTOS_V611_List_Raw_R2_Init_Item',
        'EAL6_FreeRTOS_V611_List_Raw_R3_Prefix',
        'EAL6_FreeRTOS_V611_List_Raw_R3_Tail',
        'EAL6_FreeRTOS_V611_List_Raw_R3_Prestate',
        'EAL6_FreeRTOS_V611_List_Raw_R3_Run',
        'EAL6_FreeRTOS_V611_List_Raw_R3_Count_Index',
        'EAL6_FreeRTOS_V611_List_Raw_R3_Count_Index_Post',
        'EAL6_FreeRTOS_V611_List_Raw_R3_Topology',
        'EAL6_FreeRTOS_V611_List_Raw_R3_Topology_Post',
        'EAL6_FreeRTOS_V611_List_Raw_R3_Frames',
        'EAL6_FreeRTOS_V611_List_Raw_R3_Tail_Frame',
        'EAL6_FreeRTOS_V611_List_Raw_R3_Tail_Frame_Post',
        'EAL6_FreeRTOS_V611_List_Raw_R3_Far_Frame',
        'EAL6_FreeRTOS_V611_List_Raw_R3_Master',
        'EAL6_FreeRTOS_V611_List_Raw_R4_Prestate',
        'EAL6_FreeRTOS_V611_List_Raw_R4_Locality',
        'EAL6_FreeRTOS_V611_List_Raw_R4_Run',
        'EAL6_FreeRTOS_V611_List_Raw_R4_Count_Index',
        'EAL6_FreeRTOS_V611_List_Raw_R4_Count_Index_Post',
        'EAL6_FreeRTOS_V611_List_Raw_R4_Topology',
        'EAL6_FreeRTOS_V611_List_Raw_R4_Topology_Post',
        'EAL6_FreeRTOS_V611_List_Raw_R4_Frames',
        'EAL6_FreeRTOS_V611_List_Raw_R4_Item_Frame_Post',
        'EAL6_FreeRTOS_V611_List_Raw_R4_Tail_Frame_Post',
        'EAL6_FreeRTOS_V611_List_Raw_R4_Far_Frame',
        'EAL6_FreeRTOS_V611_List_Raw_R4_Master',
        'EAL6_FreeRTOS_V611_List_Raw_R5_Relation',
        'EAL6_FreeRTOS_V611_List_Raw_R5_Interface',
        'EAL6_FreeRTOS_V611_List_Raw_R5_Cycle',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Generic_Prefix',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Dynamic_Guards',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Transfer',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Splice',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Source_Guards',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Unlink_Locality',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Remove_Relation',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Insert_Relation',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Unlink_Projection',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Insert_Source_Effects',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Ordered_Insert_Empty_Source',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Ordered_Insert_Empty_Refinement',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Remove_Metadata',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Remove_Source_Effects',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Remove_Index_Effect',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Remove_Payload_Effect',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Remove_Topology_Effect',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Insert_Post_Transformer',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Remove_Insert_Sequence',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Remove_General_Refinement',
        'EAL6_FreeRTOS_V611_List_Raw_R5_Remove_Prestate',
        'EAL6_FreeRTOS_V611_List_Raw_R5_Remove_Refinement',
        'EAL6_FreeRTOS_V611_List_Raw_Per_Function',
        'EAL6_FreeRTOS_V611_Scheduler_Parse',
        'EAL6_FreeRTOS_V611_Scheduler_Tick',
        'EAL6_FreeRTOS_V611_Scheduler_Tick_Read_Refinement',
        'EAL6_FreeRTOS_V611_Scheduler_Delay',
        'EAL6_FreeRTOS_V611_Scheduler_Roots',
        'EAL6_FreeRTOS_V611_Scheduler_Switch_Suspended_Refinement',
        'EAL6_FreeRTOS_V611_Scheduler_Increment_Tick_Suspended_Refinement',
        'EAL6_FreeRTOS_V611_Scheduler_Delay_Zero_Refinement',
        'EAL6_FreeRTOS_V611_Scheduler_Delay_Until_No_Delay_Refinement',
        'EAL6_FreeRTOS_V611_Scheduler_Universal_Validity',
        'EAL6_FreeRTOS_V611_Scheduler_Universal_Delay_Arithmetic',
        'EAL6_FreeRTOS_V611_Scheduler_Universal_Delay_Phases',
        'EAL6_FreeRTOS_V611_Scheduler_P2_Model',
        'EAL6_FreeRTOS_V611_Scheduler_Raw_List_Relabel',
        'EAL6_FreeRTOS_V611_Scheduler_P2_Generated_Layout_First',
        'EAL6_FreeRTOS_V611_Scheduler_List_ABI_Bridge',
        'EAL6_FreeRTOS_V611_Scheduler_List_ABI_Write_Bridge',
        'EAL6_FreeRTOS_V611_Scheduler_List_ABI_Read_Lenses',
        'EAL6_FreeRTOS_V611_Scheduler_P2_Raw_Relation',
        'EAL6_FreeRTOS_V611_Scheduler_P2_Source_Footprint',
        'EAL6_FreeRTOS_V611_Scheduler_P2_Remove_Source',
        'EAL6_FreeRTOS_V611_Scheduler_P2_Wake_Key',
        'EAL6_FreeRTOS_V611_Scheduler_P2_Remove_Cross_List',
        'EAL6_FreeRTOS_V611_Scheduler_P2_Remove_Wake_Frame',
        'EAL6_FreeRTOS_V611_Scheduler_P2_Insert_Transform',
        'EAL6_FreeRTOS_V611_Scheduler_P2_Insert_Frame',
        'EAL6_FreeRTOS_V611_Scheduler_P2_Insert_Source',
        'EAL6_FreeRTOS_V611_Scheduler_Ordered_Insert_General_Bridges',
        'EAL6_FreeRTOS_V611_Scheduler_Ordered_Insert_General_Source',
        'EAL6_FreeRTOS_V611_Scheduler_Ordered_Insert_General_Loop',
        'EAL6_FreeRTOS_V611_Scheduler_Ordered_Insert_General_Refinement',
        'EAL6_FreeRTOS_V611_Scheduler_Remove_Unlinked_Ownership',
        'EAL6_FreeRTOS_V611_Scheduler_Remove_Translation_General',
        'EAL6_FreeRTOS_V611_Scheduler_Delay_Endpoint_Bridge',
        'EAL6_FreeRTOS_V611_Scheduler_Delay_Suspended_Core',
        'EAL6_FreeRTOS_V611_Scheduler_Ordered_Insert_Generated_Capstone',
        'EAL6_FreeRTOS_V611_List_Insert_End_Generated_Capstone',
        'EAL6_FreeRTOS_V611_Scheduler_Insert_End_Translation_General',
        'EAL6_FreeRTOS_V611_Scheduler_List_Family_Frame_Capstone',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Inner_Source',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Outer_Scaffold',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Outer_Quiet_Bool',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Definition_Probe',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Source_Factors',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Event_Unlinked',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Generic_Unlinked_Source',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Generic_Unlinked_Family',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Event_Heap_Frame',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Generic_Unlinked_Event_Family',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Generic_Unlinked',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Top_Raised',
        'EAL6_FreeRTOS_V611_Scheduler_Family_Insert_End_Storage_Frame',
        'EAL6_FreeRTOS_V611_Scheduler_Family_Insert_End_Raw_Family',
        'EAL6_FreeRTOS_V611_Scheduler_Family_Insert_End_Subset',
        'EAL6_FreeRTOS_V611_Scheduler_Family_Insert_End_Disjoint',
        'EAL6_FreeRTOS_V611_Scheduler_Family_Insert_End_Membership',
        'EAL6_FreeRTOS_V611_Scheduler_Family_Insert_End_Shape',
        'EAL6_FreeRTOS_V611_Scheduler_Family_Insert_End_Preservation',
        'EAL6_FreeRTOS_V611_Scheduler_List_All2_Insert_After',
        'EAL6_FreeRTOS_V611_Scheduler_XList_Relabel_Insert_End',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Ready_Array_ABI',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Ready_Destination',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Ready_Select',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Ready_Insert',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Yield_Join',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Owner_Frame',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Insert_Event_Family',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Next_Head',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Body',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Insert_Owner_Frame',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Drained_Owner_Frames',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Drained_Observation',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Drained_Family',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Drained_Relabel',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Insert_Key_Frame',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Abs_Kit',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Abs_Preservation',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Reentry_Pure',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Container_Frame',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Reentry_Abs_Bridge',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Reentry_Lists',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Reentry_Rep',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Reentry_Fam',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Reentry_Gate',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Reentry_Induction',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Drain_Abs_Fold',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Pending_Control_Frame',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Gate_Base',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Phase_Adapter_Base',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Phase_Adapter_Context',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Phase_Adapter_Family',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Phase_Adapter_Owner',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Phase_Adapter_Pure_Entry',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Phase_Adapter_Capstone',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Head_Read_Nonempty',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Head_Read_Uniform',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Missed_Loop',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Outer_Compose',
        'EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_After_Event',
        'EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_Priority_Frame',
        'EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_Tail_Insert',
        'EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_Delayed_Head',
        'EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_Reentry_Pure',
        'EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_Reentry_GateH',
        'EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_Tick_Loop',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Pure_Frame',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Gate_Premises',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Source_Step',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Exit_Aware_Invariant',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Defs',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Future_Ready',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Gate_Projections',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Last_Due_Ring',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Removed_Relabel',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Head_Raw',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Head_Owner_Witness',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Gate_Decode',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Head_Ptr_Eq',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Future_Decode',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Witness_Decode',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Head_Identity',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Head_Owner',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Exit',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Bridge',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Empty_Body',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Future_Body',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Followup',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Source',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Generated_While_Core',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Generated_While_Index',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Generated_While_Terminal_Post',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Generated_While_Last_Due',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Generated_While_All_Due',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Generated_While_Zero',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Generated_While_Complete',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Generated_While_Finally',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Generated_While',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_Snapshot_Core',
        'EAL6_FreeRTOS_V611_Scheduler_Tick_Entry_Boundary',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_Snapshot_Projections',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_Snapshot_Loop_Compat',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_While_Connector',
        'EAL6_FreeRTOS_V611_Scheduler_One_Due_Tick_Exact_Globals',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Exact_Full_State_Propagation',
        'EAL6_FreeRTOS_V611_Scheduler_Tick_Wrap_Modular',
        'EAL6_FreeRTOS_V611_Scheduler_Outer_Tick_Contract',
        'EAL6_FreeRTOS_V611_Scheduler_Task_Observation_Rel',
        'EAL6_FreeRTOS_V611_Scheduler_Task_Observation_Heap_Frame',
        'EAL6_FreeRTOS_V611_Scheduler_Task_Observation_Remove_Frame',
        'EAL6_FreeRTOS_V611_Scheduler_Task_Observation_Insert_Frame',
        'EAL6_FreeRTOS_V611_Scheduler_Global_Coverage_Generic_Heap_Frame',
        'EAL6_FreeRTOS_V611_Scheduler_Global_Coverage_Event_Heap_Frame',
        'EAL6_FreeRTOS_V611_Scheduler_Global_Coverage_Optional_Event_Remove',
        'EAL6_FreeRTOS_V611_Scheduler_Generic_Root_Family_Coverage_Remove_Preserved',
        'EAL6_FreeRTOS_V611_Scheduler_Generic_Root_Coverage_Insert_End',
        'EAL6_FreeRTOS_V611_Scheduler_Generic_Event_Root_Family_Coverage_Cross_Storage',
        'EAL6_FreeRTOS_V611_Scheduler_Generic_Remove_Frames_Event_Coverage',
        'EAL6_FreeRTOS_V611_Scheduler_Generic_Insert_End_Frames_Event_Coverage',
        'EAL6_FreeRTOS_V611_Scheduler_Event_Remove_Frames_Generic_Coverage',
        'EAL6_FreeRTOS_V611_Scheduler_One_Due_Full_Family_Cutpoint_Composition',
        'EAL6_FreeRTOS_V611_Scheduler_Managed_Task_Observation_Cutpoints',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_Role_Wake_Ledgers',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_Result_Shared_Defs',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_Result_Event_Semantics',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_Result_Observation_Snapshot_Pins',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_Result_State_Assembler',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_Result_Generated_Source_Capstone',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Gate_Diagnostic',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Gate_Defs_Context',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Gate_Family_Cross',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Gate_Entry_Raw_Owner',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Gate_Capstone',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Gate_Nonlast_Source',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Gate_Strong_Bridges',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Gate_Strong_State',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Gate_Nonlast_Capstone',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_ML_Public_Wrapper',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Gate_Terminal',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_Terminal_Empty_Result',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_Terminal_Future_Source',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_Arbitrary_While_Lift',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Arbitrary_While_Defs',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Arbitrary_While_Index',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Arbitrary_While_Zero',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Arbitrary_While_Terminal_Interface',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Arbitrary_While_Terminal_Adapters',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Arbitrary_While',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Arbitrary_While_Complete',
        'EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Pure_Entry_Phase',
        'EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Prefix_Source_Factors',
        'EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Prefix_Role_Exact',
        'EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Prefix_Head_Exact',
        'EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Prefix_Source_Exact',
        'EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Managed_Entry_Assembler',
        'EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Snapshot_Transport',
        'EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Pointer_Bridge',
        'EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Prefix_Capstone',
        'EAL6_FreeRTOS_V611_Scheduler_Outer_Tick_Final_Connector',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Invariants',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Snapshots',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Preservation',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Pointer_Bridge',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Due_Step_Bridges',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Due_Step_Role_Wake',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Due_Step_Family_State',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Due_Step_Snapshot_State',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Due_Step_Strong_State_Core',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Due_Step_Nonlast_Capstone',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Terminal_Empty_State',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Terminal_Empty_Result',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Terminal_Empty_Bare',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Terminal_Empty_Finally',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Terminal_Future_Ready',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Terminal_Future_State',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Terminal_Future_Result',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Terminal_Future_Bare',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Terminal_Future_Finally',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While_Defs',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While_Index',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While_Zero',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While_Terminal_Defs',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While_Terminal_Facts',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While_Terminal_Public',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While_Terminal_Adapter',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While_Complete',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Pure_Entry',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Snapshot_Core',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Snapshot_Tasks',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Managed_Gate_Context',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Managed_Gate_Pure',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Managed_Gate_Raw',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Managed_Entry_Defs',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Managed_Entry_Assembler',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Prefix_Capstone',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Pipeline_Capstone',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Outer_Tick_Connector',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Boundary_Closure',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Trace',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Rel_Spec_Probe',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Core_Closure',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_VList_Remove',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_VList_Insert_End',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Event_Dispatch',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Top_Ready_Tail_Join',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Top_Ready_Tail',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_After_Generic',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Loop_Body',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_While_Factor',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Finally_Factor',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Role_Source',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Prefix_Source',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Unlocked_Source',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Whole_Tick_Rel_Spec',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Overlay',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Overlay_Capstone',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Missed_Decrement_Frame',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Missed_Body_Capstone',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Replay_Horizon_Abs',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Replay_Arithmetic_Bridge',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Replay_Safe_Loop',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Replay_Progress',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Replay_Body_Outcomes',
        'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Replay_First_Unsafe',
        'EAL6_FreeRTOS_V611_Scheduler_Event_Root_Family_Rel',
        'EAL6_FreeRTOS_V611_Scheduler_Event_Root_Family_Remove_Decoder_Remove1',
        'EAL6_FreeRTOS_V611_Scheduler_Event_Root_Family_Remove_Predecessor',
        'EAL6_FreeRTOS_V611_Scheduler_Event_Root_Family_Remove_Cursor',
        'EAL6_FreeRTOS_V611_Scheduler_Event_Root_Family_Remove_Keys',
        'EAL6_FreeRTOS_V611_Scheduler_Event_Root_Family_Remove_Relabel',
        'EAL6_FreeRTOS_V611_Scheduler_Event_Root_Family_Remove_Pre_Rel',
        'EAL6_FreeRTOS_V611_Scheduler_Event_Root_Family_Remove_Payload_Frame',
        'EAL6_FreeRTOS_V611_Scheduler_Event_Root_Family_Remove_Physical',
        'EAL6_FreeRTOS_V611_Scheduler_Event_Root_Family_Remove_Container_Rep',
        'EAL6_FreeRTOS_V611_Scheduler_Event_Root_Family_Remove_Key_Rep',
        'EAL6_FreeRTOS_V611_Scheduler_Event_Root_Family_Remove_Root_Rep',
        'EAL6_FreeRTOS_V611_Scheduler_Event_Root_Family_Remove_Preservation',
        'EAL6_FreeRTOS_V611_Scheduler_Family_Remove_Core',
        'EAL6_FreeRTOS_V611_Scheduler_Node_Kind_Family_Remove_Preservation',
        'EAL6_FreeRTOS_V611_Scheduler_Generic_Root_Universe_Base',
        'EAL6_FreeRTOS_V611_Scheduler_Generic_Root_Universe_Coverage_Core',
        'EAL6_FreeRTOS_V611_Scheduler_Generic_Root_Universe_Coverage',
        'EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Scaffold',
        'EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_Base',
        'EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_Entry',
        'EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_Post',
        'EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_Generated',
        'EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases',
        'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Invariant',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Pending_Drain_Phases',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Pending_Drain_Gate_Relation_Base',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Pending_Drain_Gate_Relation_Decoder',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Pending_Drain_Gate_Relation_Coverage_Observation',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Pending_Drain_Gate_Relation_Coverage_Count',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Pending_Drain_Gate_Relation_Coverage_Ownership',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Pending_Drain_Gate_Relation_Coverage_Freshness',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Pending_Drain_Gate_Relation_Coverage_Event',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Pending_Drain_Gate_Relation_Coverage',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Pending_Drain_Gate_Relation',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Pending_Drain_Gate',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Missed_Tick_Replay_Core',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Missed_Tick_Replay_Frame',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Missed_Tick_Replay_Steps_Invariant',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Missed_Tick_Replay_Tick_Wrap',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Missed_Tick_Replay_Yield_OR',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Missed_Tick_Replay_Pending_Join',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Missed_Tick_Replay_Quiet_Encoding',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Missed_Tick_Replay_Yield_Interface',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_Missed_Tick_Replay',
        'EAL6_FreeRTOS_V611_Scheduler_Concurrent_State',
        'EAL6_FreeRTOS_V611_Scheduler_Concurrent_Environment_Step',
        'EAL6_FreeRTOS_V611_Scheduler_Concurrent_Environment_Closure',
        'EAL6_FreeRTOS_V611_Scheduler_Concurrent_Program_Step',
        'EAL6_FreeRTOS_V611_Scheduler_Concurrent_Interleaving',
        'EAL6_FreeRTOS_V611_Scheduler_Concurrent_Cutpoint',
        'EAL6_FreeRTOS_V611_Scheduler_Concurrent_Contract_Interface',
        'EAL6_FreeRTOS_V611_Scheduler_Universal_Capacity',
        'EAL6_FreeRTOS_V611_Scheduler_Universal_Geometry',
        'EAL6_FreeRTOS_V611_Scheduler_P2_Insert_Refinement',
        'EAL6_FreeRTOS_V611_Scheduler_P2_Control_Leaves',
        'EAL6_FreeRTOS_V611_Scheduler_Resume_General_Relation',
        'EAL6_FreeRTOS_V611_Scheduler_P2_Delay_Source',
        'EAL6_FreeRTOS_V611_Scheduler_P2_Post_Relation',
        'EAL6_FreeRTOS_V611_Scheduler_P2_Delay_Refinement',
        'EAL6_FreeRTOS_V611_Scheduler_P2_Layout_No_Go',
        'EAL6_FreeRTOS_V611_Scheduler_P2_Frozen_Root_Probe',
        'EAL6_FreeRTOS_V611_Scheduler_P2_Frozen_Static_Layout',
        'EAL6_FreeRTOS_V611_Scheduler_P2_Frozen_Dynamic_Geometry',
        'EAL6_FreeRTOS_V611_Scheduler_P2_Frozen_Preimage',
        'EAL6_FreeRTOS_V611_List_Raw_R6_Initialise_Insert_Remove_Sequence',
        'EAL6_FreeRTOS_V611_Capstone_Assumption_Audit'
    )]
    [string]$Session = 'EAL6_FreeRTOS_V611_List_Smoke'
)

$ErrorActionPreference = 'Stop'

$projectRoot = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
$theoryRoot = Join-Path $projectRoot 'theories'
$runRoot = Join-Path $projectRoot 'runs'
$runDir = Join-Path $runRoot $RunId
$isabelleHome = 'C:\Isabelle2025-2\Isabelle2025-2'
$isabelleTool = Join-Path $isabelleHome 'bin\isabelle'
$cygwinBash = Join-Path $isabelleHome 'contrib\cygwin\bin\bash.exe'
$autoCorresRoot = 'C:\afp25\afp-2026-07-21\thys\AutoCorres2'
$simplRoot = 'C:\afp25\afp-2026-07-21\thys\Simpl'
$wordLibRoot = 'C:\afp25\afp-2026-07-21\thys\Word_Lib'
$preparePatchedAutoCorres = Join-Path $PSScriptRoot 'prepare-patched-autocorres2.ps1'
$artifactBuild = Join-Path $projectRoot 'artifacts\frozen_p2_layout\build_and_check.ps1'
$artifactLedger = Join-Path $projectRoot 'artifacts\frozen_p2_layout\output\layout_ledger.json'
$artifactElf = Join-Path $projectRoot 'artifacts\frozen_p2_layout\output\frozen_p2_layout.elf'
$addressGenerator = Join-Path $projectRoot 'tools\generate_p2_root_address_config.py'
$generatedAddressConfig = Join-Path $projectRoot 'build\generated\P2_Root_Address_Config.ML'
$expectedArtifactElfSha256 =
    'dc830e50513384d712e0d1c68cb198ea656365f673d021c452d7d7ebd45c045a'
$isabelleHomeUser = Join-Path $env:USERPROFILE '.isabelle\Isabelle2025-2'
$session = $Session
$localSessionRoots = if ($CentralOnly) {
    @()
} else {
switch ($session) {
    'EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Scaffold' {
        @(Join-Path $theoryRoot 'scheduler_unlocked_tick_scaffold')
    }
    'EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_Base' {
        @(
            (Join-Path $theoryRoot 'scheduler_unlocked_tick_scaffold'),
            (Join-Path $theoryRoot 'scheduler_one_due_task_phases')
        )
    }
    'EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_Entry' {
        @(
            (Join-Path $theoryRoot 'scheduler_unlocked_tick_scaffold'),
            (Join-Path $theoryRoot 'scheduler_one_due_task_phases')
        )
    }
    'EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_Post' {
        @(
            (Join-Path $theoryRoot 'scheduler_unlocked_tick_scaffold'),
            (Join-Path $theoryRoot 'scheduler_one_due_task_phases')
        )
    }
    'EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_Generated' {
        @(
            (Join-Path $theoryRoot 'scheduler_unlocked_tick_scaffold'),
            (Join-Path $theoryRoot 'scheduler_one_due_task_phases')
        )
    }
    'EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases' {
        @(
            (Join-Path $theoryRoot 'scheduler_unlocked_tick_scaffold'),
            (Join-Path $theoryRoot 'scheduler_one_due_task_phases')
        )
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Invariant' {
        @(Join-Path $theoryRoot 'scheduler_due_prefix_invariant')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Generic_Root_Universe_Coverage' {
        @(Join-Path $theoryRoot 'scheduler_generic_root_universe_coverage')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Generic_Root_Universe_Base' {
        @(Join-Path $theoryRoot 'scheduler_generic_root_universe_coverage')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Generic_Root_Universe_Coverage_Core' {
        @(Join-Path $theoryRoot 'scheduler_generic_root_universe_coverage')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Pending_Drain_Phases' {
        @(Join-Path $theoryRoot 'scheduler_resume_pending_drain_phases')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Pending_Drain_Gate_Relation_Base' {
        @(Join-Path $theoryRoot 'scheduler_resume_pending_drain_phases')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Pending_Drain_Gate_Relation_Decoder' {
        @(Join-Path $theoryRoot 'scheduler_resume_pending_drain_phases')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Pending_Drain_Gate_Relation_Coverage_Observation' {
        @(Join-Path $theoryRoot 'scheduler_resume_pending_drain_phases')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Pending_Drain_Gate_Relation_Coverage_Count' {
        @(Join-Path $theoryRoot 'scheduler_resume_pending_drain_phases')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Pending_Drain_Gate_Relation_Coverage_Ownership' {
        @(Join-Path $theoryRoot 'scheduler_resume_pending_drain_phases')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Pending_Drain_Gate_Relation_Coverage_Freshness' {
        @(Join-Path $theoryRoot 'scheduler_resume_pending_drain_phases')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Pending_Drain_Gate_Relation_Coverage_Event' {
        @(Join-Path $theoryRoot 'scheduler_resume_pending_drain_phases')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Pending_Drain_Gate_Relation_Coverage' {
        @(Join-Path $theoryRoot 'scheduler_resume_pending_drain_phases')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Pending_Drain_Gate_Relation' {
        @(Join-Path $theoryRoot 'scheduler_resume_pending_drain_phases')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Pending_Drain_Gate' {
        @(Join-Path $theoryRoot 'scheduler_resume_pending_drain_phases')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Missed_Tick_Replay' {
        @(
            (Join-Path $theoryRoot 'scheduler_due_prefix_invariant'),
            (Join-Path $theoryRoot 'scheduler_resume_outer_quiet_bool'),
            (Join-Path $theoryRoot 'scheduler_resume_missed_tick_replay')
        )
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Missed_Tick_Replay_Core' {
        @(
            (Join-Path $theoryRoot 'scheduler_due_prefix_invariant'),
            (Join-Path $theoryRoot 'scheduler_resume_outer_quiet_bool'),
            (Join-Path $theoryRoot 'scheduler_resume_missed_tick_replay')
        )
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Missed_Tick_Replay_Frame' {
        @(
            (Join-Path $theoryRoot 'scheduler_due_prefix_invariant'),
            (Join-Path $theoryRoot 'scheduler_resume_outer_quiet_bool'),
            (Join-Path $theoryRoot 'scheduler_resume_missed_tick_replay')
        )
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Missed_Tick_Replay_Steps_Invariant' {
        @(
            (Join-Path $theoryRoot 'scheduler_due_prefix_invariant'),
            (Join-Path $theoryRoot 'scheduler_resume_outer_quiet_bool'),
            (Join-Path $theoryRoot 'scheduler_resume_missed_tick_replay')
        )
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Missed_Tick_Replay_Tick_Wrap' {
        @(
            (Join-Path $theoryRoot 'scheduler_due_prefix_invariant'),
            (Join-Path $theoryRoot 'scheduler_resume_outer_quiet_bool'),
            (Join-Path $theoryRoot 'scheduler_resume_missed_tick_replay')
        )
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Missed_Tick_Replay_Yield_Interface' {
        @(
            (Join-Path $theoryRoot 'scheduler_due_prefix_invariant'),
            (Join-Path $theoryRoot 'scheduler_resume_outer_quiet_bool'),
            (Join-Path $theoryRoot 'scheduler_resume_missed_tick_replay')
        )
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Missed_Tick_Replay_Yield_OR' {
        @(
            (Join-Path $theoryRoot 'scheduler_due_prefix_invariant'),
            (Join-Path $theoryRoot 'scheduler_resume_outer_quiet_bool'),
            (Join-Path $theoryRoot 'scheduler_resume_missed_tick_replay')
        )
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Missed_Tick_Replay_Pending_Join' {
        @(
            (Join-Path $theoryRoot 'scheduler_due_prefix_invariant'),
            (Join-Path $theoryRoot 'scheduler_resume_outer_quiet_bool'),
            (Join-Path $theoryRoot 'scheduler_resume_missed_tick_replay')
        )
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Missed_Tick_Replay_Quiet_Encoding' {
        @(
            (Join-Path $theoryRoot 'scheduler_due_prefix_invariant'),
            (Join-Path $theoryRoot 'scheduler_resume_outer_quiet_bool'),
            (Join-Path $theoryRoot 'scheduler_resume_missed_tick_replay')
        )
    }
    'EAL6_FreeRTOS_V611_Scheduler_Concurrent_Contract_Interface' {
        @(Join-Path $theoryRoot 'scheduler_concurrent_contract_interface')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Concurrent_State' {
        @(Join-Path $theoryRoot 'scheduler_concurrent_contract_interface')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Concurrent_Environment_Step' {
        @(Join-Path $theoryRoot 'scheduler_concurrent_contract_interface')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Concurrent_Environment_Closure' {
        @(Join-Path $theoryRoot 'scheduler_concurrent_contract_interface')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Concurrent_Program_Step' {
        @(Join-Path $theoryRoot 'scheduler_concurrent_contract_interface')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Concurrent_Interleaving' {
        @(Join-Path $theoryRoot 'scheduler_concurrent_contract_interface')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Concurrent_Cutpoint' {
        @(Join-Path $theoryRoot 'scheduler_concurrent_contract_interface')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Outer_Quiet_Bool' {
        @(Join-Path $theoryRoot 'scheduler_resume_outer_quiet_bool')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Definition_Probe' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Source_Factors' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Event_Unlinked' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Generic_Unlinked_Source' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Generic_Unlinked_Family' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Event_Heap_Frame' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Generic_Unlinked_Event_Family' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Generic_Unlinked' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Top_Raised' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Family_Insert_End_Storage_Frame' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Family_Insert_End_Raw_Family' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Family_Insert_End_Subset' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Family_Insert_End_Disjoint' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Family_Insert_End_Membership' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Family_Insert_End_Shape' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Family_Insert_End_Preservation' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_List_All2_Insert_After' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_XList_Relabel_Insert_End' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Ready_Array_ABI' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Ready_Destination' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Ready_Select' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Ready_Insert' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Yield_Join' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Owner_Frame' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Insert_Event_Family' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Next_Head' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Body' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Insert_Owner_Frame' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Drained_Owner_Frames' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Drained_Observation' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Drained_Family' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Drained_Relabel' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Insert_Key_Frame' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Abs_Kit' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Abs_Preservation' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Reentry_Pure' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Container_Frame' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Reentry_Abs_Bridge' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Reentry_Lists' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Reentry_Rep' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Reentry_Fam' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Reentry_Gate' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Reentry_Induction' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Drain_Abs_Fold' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Pending_Control_Frame' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Gate_Base' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Phase_Adapter_Base' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Phase_Adapter_Context' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Phase_Adapter_Family' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Phase_Adapter_Owner' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Phase_Adapter_Pure_Entry' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Phase_Adapter_Capstone' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Head_Read_Nonempty' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Head_Read_Uniform' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Missed_Loop' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Outer_Compose' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_After_Event' {
        @()
    }
    'EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_Priority_Frame' {
        @()
    }
    'EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_Tail_Insert' {
        @()
    }
    'EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_Delayed_Head' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_Reentry_Pure' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_Reentry_GateH' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_One_Due_Task_Phases_Tick_Loop' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Pure_Frame' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Gate_Premises' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Source_Step' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Exit_Aware_Invariant' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Defs' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Future_Ready' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Gate_Projections' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Last_Due_Ring' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Removed_Relabel' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Head_Raw' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Head_Owner_Witness' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Gate_Decode' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Head_Ptr_Eq' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Future_Decode' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Witness_Decode' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Head_Identity' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Head_Owner' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Exit' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Bridge' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Empty_Body' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Future_Body' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Followup' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Terminal_Source' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Generated_While_Core' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Generated_While_Index' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Generated_While_Terminal_Post' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Generated_While_Last_Due' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Generated_While_All_Due' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Generated_While_Zero' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Generated_While_Complete' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Generated_While_Finally' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Generated_While' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_Snapshot_Core' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Tick_Entry_Boundary' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_Snapshot_Projections' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_Snapshot_Loop_Compat' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_While_Connector' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_One_Due_Tick_Exact_Globals' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Exact_Full_State_Propagation' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Tick_Wrap_Modular' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Outer_Tick_Contract' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Task_Observation_Heap_Frame' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Task_Observation_Remove_Frame' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Task_Observation_Insert_Frame' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Global_Coverage_Generic_Heap_Frame' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Global_Coverage_Event_Heap_Frame' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Global_Coverage_Optional_Event_Remove' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Generic_Root_Family_Coverage_Remove_Preserved' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Generic_Root_Coverage_Insert_End' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Generic_Event_Root_Family_Coverage_Cross_Storage' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Generic_Remove_Frames_Event_Coverage' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Generic_Insert_End_Frames_Event_Coverage' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Event_Remove_Frames_Generic_Coverage' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_One_Due_Full_Family_Cutpoint_Composition' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Managed_Task_Observation_Cutpoints' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_Role_Wake_Ledgers' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_Result_Shared_Defs' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_Result_Event_Semantics' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_Result_Observation_Snapshot_Pins' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_Result_State_Assembler' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_Result_Generated_Source_Capstone' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Gate_Diagnostic' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Gate_Defs_Context' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Gate_Family_Cross' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Gate_Entry_Raw_Owner' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Gate_Capstone' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Gate_Nonlast_Source' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Gate_Strong_Bridges' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Gate_Strong_State' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Gate_Nonlast_Capstone' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_ML_Public_Wrapper' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Gate_Terminal' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_Terminal_Empty_Result' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_Terminal_Future_Source' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_Arbitrary_While_Lift' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Arbitrary_While_Defs' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Arbitrary_While_Index' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Arbitrary_While_Zero' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Arbitrary_While_Terminal_Interface' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Arbitrary_While_Terminal_Adapters' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Arbitrary_While' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Arbitrary_While_Complete' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Pure_Entry_Phase' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Prefix_Source_Factors' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Prefix_Role_Exact' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Prefix_Head_Exact' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Prefix_Source_Exact' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Managed_Entry_Assembler' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Snapshot_Transport' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Pointer_Bridge' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Prefix_Capstone' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Outer_Tick_Final_Connector' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Invariants' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Snapshots' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Preservation' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Pointer_Bridge' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Due_Step_Bridges' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Due_Step_Role_Wake' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Due_Step_Family_State' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Due_Step_Snapshot_State' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Due_Step_Strong_State_Core' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Due_Step_Nonlast_Capstone' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Terminal_Empty_State' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Terminal_Empty_Result' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Terminal_Empty_Bare' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Terminal_Empty_Finally' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Terminal_Future_Ready' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Terminal_Future_State' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Terminal_Future_Result' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Terminal_Future_Bare' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Terminal_Future_Finally' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While_Defs' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While_Index' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While_Zero' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While_Terminal_Defs' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While_Terminal_Facts' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While_Terminal_Public' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While_Terminal_Adapter' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Managed_While_Complete' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Pure_Entry' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Snapshot_Core' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Snapshot_Tasks' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Managed_Gate_Context' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Managed_Gate_Pure' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Managed_Gate_Raw' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Managed_Entry_Defs' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Managed_Entry_Assembler' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Prefix_Capstone' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Unlocked_Pipeline_Capstone' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Outer_Tick_Connector' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Boundary_Closure' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Trace' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Rel_Spec_Probe' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Core_Closure' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_VList_Remove' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_VList_Insert_End' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Event_Dispatch' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Top_Ready_Tail_Join' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Top_Ready_Tail' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_After_Generic' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Loop_Body' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_While_Factor' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Finally_Factor' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Role_Source' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Prefix_Source' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Unlocked_Source' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Whole_Tick_Rel_Spec' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Overlay' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Overlay_Capstone' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Missed_Decrement_Frame' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Missed_Body_Capstone' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Replay_Horizon_Abs' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Replay_Arithmetic_Bridge' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Replay_Safe_Loop' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Replay_Progress' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Replay_Body_Outcomes' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Replay_First_Unsafe' {
        @(Join-Path $theoryRoot 'scheduler_resume_generated_vcg')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Family_Remove_Core' {
        @(Join-Path $theoryRoot 'scheduler_family_remove_preservation')
    }
    'EAL6_FreeRTOS_V611_Scheduler_Node_Kind_Family_Remove_Preservation' {
        @(Join-Path $theoryRoot 'scheduler_family_remove_preservation')
    }
    default { @() }
}
}

foreach ($required in @(
    $isabelleTool, $cygwinBash, $autoCorresRoot, $simplRoot, $wordLibRoot,
    $preparePatchedAutoCorres, $artifactBuild, $addressGenerator,
    $theoryRoot
)) {
    if (-not (Test-Path -LiteralPath $required)) {
        throw "Required path is missing: $required"
    }
}

$artifactBuildOutput = & $artifactBuild -TimeoutSeconds 120

$addressGeneratorOutput = & python $addressGenerator `
    --project-root $projectRoot `
    --ledger $artifactLedger `
    --elf $artifactElf `
    --expected-elf-sha256 $expectedArtifactElfSha256 `
    --output $generatedAddressConfig
if ($LASTEXITCODE -ne 0) {
    throw "Generating the CParser address configuration failed with exit code $LASTEXITCODE"
}

$artifactElfSha256 = (Get-FileHash -Algorithm SHA256 -LiteralPath $artifactElf).Hash
$artifactLedgerSha256 = (Get-FileHash -Algorithm SHA256 -LiteralPath $artifactLedger).Hash
$generatedAddressConfigSha256 =
    (Get-FileHash -Algorithm SHA256 -LiteralPath $generatedAddressConfig).Hash

$patchedAutoCorresOutput = & $preparePatchedAutoCorres
$patchedAutoCorresRoot =
    (Resolve-Path -LiteralPath ($patchedAutoCorresOutput | Select-Object -Last 1)).Path

New-Item -ItemType Directory -Force -Path $runDir | Out-Null

$stdoutPath = Join-Path $runDir 'stdout.log'
$stderrPath = Join-Path $runDir 'stderr.log'
$statusPath = Join-Path $runDir 'status.txt'
$commandPath = Join-Path $runDir 'command.txt'

function ConvertTo-CygwinPath([string]$WindowsPath) {
    $fullPath = [IO.Path]::GetFullPath($WindowsPath)
    if ($fullPath -notmatch '^[A-Za-z]:\\') {
        throw "Expected an absolute drive path: $WindowsPath"
    }
    $drive = $fullPath.Substring(0, 1).ToLowerInvariant()
    $rest = $fullPath.Substring(3).Replace('\', '/')
    return "/cygdrive/$drive/$rest"
}

$isabelleToolCygwin = ConvertTo-CygwinPath $isabelleTool
$patchedAutoCorresRootCygwin = ConvertTo-CygwinPath $patchedAutoCorresRoot
$simplRootCygwin = ConvertTo-CygwinPath $simplRoot
$wordLibRootCygwin = ConvertTo-CygwinPath $wordLibRoot
$theoryRootCygwin = ConvertTo-CygwinPath $theoryRoot
$localSessionOption = (($localSessionRoots | ForEach-Object {
    $localSessionRootCygwin = ConvertTo-CygwinPath $_
    "-d '$localSessionRootCygwin'"
}) -join ' ')
if ($localSessionOption.Length -gt 0) {
    $localSessionOption += ' '
}
$bashCommand = "exec '$isabelleToolCygwin' build " +
    "-d '$simplRootCygwin' -d '$wordLibRootCygwin' " +
    "-d '$patchedAutoCorresRootCygwin' -d '$theoryRootCygwin' " +
    $localSessionOption +
    "-o quick_and_dirty=false -j 1 '$session'"
Set-Content -LiteralPath $commandPath -Encoding utf8 -Value (
    "`"$cygwinBash`" --login -c `"$bashCommand`""
)

$stopwatch = [Diagnostics.Stopwatch]::StartNew()
$timedOut = $false
$process = [Diagnostics.Process]::new()
$startInfo = [Diagnostics.ProcessStartInfo]::new()
$startInfo.FileName = $cygwinBash
$startInfo.WorkingDirectory = $projectRoot
$startInfo.UseShellExecute = $false
$startInfo.CreateNoWindow = $true
$startInfo.RedirectStandardOutput = $true
$startInfo.RedirectStandardError = $true
$startInfo.Environment['CHERE_INVOKING'] = 'true'
$startInfo.Environment['LANG'] = 'en_US.UTF-8'
[void]$startInfo.ArgumentList.Add('--login')
[void]$startInfo.ArgumentList.Add('-c')
[void]$startInfo.ArgumentList.Add($bashCommand)
$process.StartInfo = $startInfo

try {
    [void]$process.Start()
    $stdoutTask = $process.StandardOutput.ReadToEndAsync()
    $stderrTask = $process.StandardError.ReadToEndAsync()

    if (-not $process.WaitForExit($TimeoutSeconds * 1000)) {
        $timedOut = $true
        & "$env:SystemRoot\System32\taskkill.exe" /PID $process.Id /T /F | Out-Null
        $process.WaitForExit()
    }

    Set-Content -LiteralPath $stdoutPath -Encoding utf8 -Value (
        $stdoutTask.GetAwaiter().GetResult()
    )
    Set-Content -LiteralPath $stderrPath -Encoding utf8 -Value (
        $stderrTask.GetAwaiter().GetResult()
    )
}
finally {
    $stopwatch.Stop()
}

$exitCode = if ($timedOut) { 124 } else { $process.ExitCode }
$stdoutHash = if (Test-Path -LiteralPath $stdoutPath) {
    (Get-FileHash -Algorithm SHA256 -LiteralPath $stdoutPath).Hash
} else { 'MISSING' }
$stderrHash = if (Test-Path -LiteralPath $stderrPath) {
    (Get-FileHash -Algorithm SHA256 -LiteralPath $stderrPath).Hash
} else { 'MISSING' }

$status = @(
    "run_id=$RunId",
    "session=$session",
    "pid=$($process.Id)",
    "quick_and_dirty=false",
    "timeout_seconds=$TimeoutSeconds",
    "timed_out=$($timedOut.ToString().ToLowerInvariant())",
    "exit_code=$exitCode",
    "elapsed_seconds=$([Math]::Round($stopwatch.Elapsed.TotalSeconds, 3))",
    "stdout_sha256=$stdoutHash",
    "stderr_sha256=$stderrHash",
    "isabelle_home_user=%USERPROFILE%/.isabelle/Isabelle2025-2"
    "frozen_layout_elf_sha256=$artifactElfSha256"
    "frozen_layout_ledger_sha256=$artifactLedgerSha256"
    "generated_address_config_sha256=$generatedAddressConfigSha256"
)
Set-Content -LiteralPath $statusPath -Encoding utf8 -Value $status

Write-Output "run_dir=$runDir"
Write-Output "exit_code=$exitCode"
Write-Output "elapsed_seconds=$([Math]::Round($stopwatch.Elapsed.TotalSeconds, 3))"

exit $exitCode
