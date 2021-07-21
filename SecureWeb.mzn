% 
% Secure Web Container for MiniZinc
%
% This MiniZinc model was created by David Bogdan, bogdan.david02@e-uvt.ro
%

% ------------ INPUT VARIABLES -------------

% Maximum number of VMs required taken from ComputeVM
int: VM;

% Number of components of the application
int: NoComponents;

% Number of hardware requirements for a component (e.g. CPU, Memory, Storage, etc.)
int: HardwareREQ;

% Number of VM Offers
int: VMOffers;

% Minimum number of instances to be deployed
int: IDs = 1;

% Requirements for each component
array[1..NoComponents, 1..HardwareREQ] of int: CompREQ;

% VM specifications
array[1..VMOffers, 1..HardwareREQ] of int: VMSpecs;

% Prices of VMs
array[1..VMOffers] of int: VMPrice;

% Global variable used in conflict constraints
set of int: S = { i | i in 1..NoComponents};

% --------- DECISION VARIABLES ----------

% Assignment matrix
array[1..NoComponents, 1..VM] of var 0..1: AssignmentMatrix;  % a

% Type of VM (which component is located there)
array[1..VM] of var 1..VMOffers: VMType; % t

% Occupancy vector
array[1..VM] of var 0..1: OccupancyChart; % v

% Data of the virtual machine on which the ith component has been deployed
array[1..VM] of var 1..64: CPU;
array[1..VM] of var 1700..976000: Memory;
array[1..VM] of var 1000..24000: Storage;
array[1..VM] of var 0..16000: Price;

% ----- CONSTRAINTS -----


% Checks whether a component has been deployed or not
function var int: isDeployed(int: compID) =
    if(sum(k in 1..VM)(AssignmentMatrix[compID,k]) > 0) then 1 else 0 endif;
    
% Ensures the NULL (0) Type is reserved only for unused virtual machines
predicate setType() =
    forall(k in 1..VM)(sum(i in 1..NoComponents) 
          (AssignmentMatrix[i,k]) >= 1 -> VMType[k] > 0);   
          
% Ensures used VMs have their occupancy vector set
predicate occupancy() =
    forall(k in 1..VM)(sum(i in 1..NoComponents) 
          (AssignmentMatrix[i,k]) >= 1 -> OccupancyChart[k] = 1);
          
% Ensures hardware requirements are met for each component
predicate capacity() =
    forall(k in 1..VM, h in 1..HardwareREQ)  
          (sum(i in 1..NoComponents) 
          (AssignmentMatrix[i,k] * CompREQ[i,h]) <= VMSpecs[VMType[k],h]);
          
% Links resource arrays to VMs
predicate link() =
    forall(k in 1..VM, o in 1..VMOffers)
          ((OccupancyChart[k] == 1 /\ VMType[k] == o) ->
          (CPU[k] == VMSpecs[o,1] /\ Memory[k] == VMSpecs[o,2] /\
           Storage[k] == VMSpecs[o,3] /\ Price[k] == VMPrice[o]));

predicate basicAllocation (var set of int:exclusive) 
  = forall( i in S diff exclusive)(sum (k in 1..VM) (AssignmentMatrix[i, k]) >= 1);

predicate nullType() = 
    forall(k in 1..VM)(sum(i in 1..NoComponents) 
          (AssignmentMatrix[i,k]) == 0 -> VMType[k] = 0);

predicate lowerBound(int: compID, int: compID2, int: bound) =
    sum(k in 1..VM)(AssignmentMatrix[compID,k]) + sum(k in 1..VM)(AssignmentMatrix[compID2, k]) >= bound;

predicate upperBound(int: compID, int: bound) =
    sum(k in 1..VM) (AssignmentMatrix[compID, k]) <= bound;
    
predicate equalBound(int: compID, int: bound) =
    sum(k in 1..VM) (AssignmentMatrix[compID, k]) == bound;
            
predicate requireProvide(int: compID1, int: compID2, 
                         int: NoInstID1, int: NoInstID2) =
    NoInstID1 * sum(k in 1..VM) (AssignmentMatrix[compID1, k]) <=
    NoInstID2 * sum(k in 1..VM) (AssignmentMatrix[compID2, k]);
    
predicate provide(int: compID1, int: compID2, int: NoInstID1) =
    sum(k in 1..VM) (AssignmentMatrix[compID1, k]) <=
    sum(k in 1..VM) (AssignmentMatrix[compID2, k]) * NoInstID1;
    
predicate conflict(int: compID, var set of int: conflicts) =
    forall(k in 1..VM, i in conflicts)
          (AssignmentMatrix[compID, k] + AssignmentMatrix[i, k] <= 1);
   
% ----- APPLYING CONSTRAINTS TO MODEL -----


% General constraints

% Removed basicAllocation, as it takes a parameter components which are in exclusiveDeployment
% (which there are none), and thus S - exclusive = S, so it forces each component to be present
% at least once, whereas we can have 3 Apache instances and 0 Ngnix in a valid solution.

%constraint basicAllocation({});


constraint setType();
constraint occupancy();
constraint capacity();
constraint link();
constraint nullType();

% Problem-specific constraints
constraint equalBound(1, 1);         % Exactly 1 balancer per application
constraint lowerBound(2, 3, 3);      % At least 3 Apache + Ngnix per application    

constraint conflict(1, {2,3,4,5});  % Balancer has its own VM
constraint conflict(4, {1,2,3,5});  % IDSServer has its own VM
constraint conflict(2, {3});        % No Apache and Ngnix on same VM

constraint requireProvide(4, 5, 1, 10);  % 1 IDSServer for every 10 agents
constraint sum(k in 1..VM) (AssignmentMatrix[5,k]) > 0 -> sum(k in 1..VM)(AssignmentMatrix[4,k]) > 0; % Ensures 1 server for first 10 agents

% 1 Agent must be present of every VM containing Apache or Ngnix ( FULL-DEPLOYMENT )
constraint forall(k in 1..VM) (AssignmentMatrix[2,k] + AssignmentMatrix[3,k] == AssignmentMatrix[5,k]);

% Solve
solve minimize sum(p in Price) (p);

output [ "\(AssignmentMatrix[i,j])" ++ (if (j == VM) then "\n" else " " endif) | i in 1..NoComponents, j in 1.. VM];