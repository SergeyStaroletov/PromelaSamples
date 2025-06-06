%%%-------------------------------------------------------------------
%%% @author Sergey Staroletov
%%% @copyright (C) 2019, 2025, serg_soft@mail.ru
%%% @doc
%%% Simplified POET protocol demo
%%% Discussed in my book [in Russian]
%%% https://www.researchgate.net/publication/336640317_Functional_Languages_for_Distributive_Systems_in_Russian
%%% @end
%%%-------------------------------------------------------------------
-module(poet).
-author("sergey").

%% API
-export([main/0]).

% function to return 1, that the 1st argument is equal to the 2nd
condi(C, C) -> 1;
condi(C, V) when C /= V -> 0.

%  calculation of the number of processes with specified statuses
calcP(none, P) -> P;
calcP(I, P) ->
  {_, V, Inew} = maps:next(I),
  calcP(Inew, P + condi(V, V)).

calcLeader(none, P) -> P;
calcLeader(I, P) ->
  {_, V, Inew} = maps:next(I),
  calcLeader(Inew, P + condi(V, state_mineblock)).

calcNoLeader(none, P) -> P;
calcNoLeader(I, P) ->
  {_, V, Inew} = maps:next(I),
  calcNoLeader(Inew, P + condi(V, state_nonmineblock) + condi(V, state_init)).


% Function for network emulation
% receives messages and returns statuses
% State contains a tuple of network status and map pid-> status for all nodes
% Blocks stores the number of the current block
network(State, Blocks)->
  receive
    {getPCount, Sender} ->  {_, Map} = State, Sender ! Temp = calcP(maps:iterator(Map), 0),
      io:format("[network] sending process count = ~w...~n", [Temp]),
      network(State, Blocks);
    {getLeaderCount, Sender} -> {_, Map} = State, Sender ! Temp = calcLeader(maps:iterator(Map), 0),
      io:format("[network] sending leader count = ~w...~n", [Temp]),
      network(State, Blocks);
    {getNonLeaderCount, Sender} -> {_, Map} = State, Sender ! Temp =  calcNoLeader(maps:iterator(Map), 0),
      io:format("[network] sending non-leader count = ~w...~n", [Temp]),
      network(State, Blocks);
    {setGeneralState, _Sender, NewGeneralState} ->  {_, OtherData} = State,
      NewState = {NewGeneralState, OtherData},
      io:format("[network] set general state = ~w...~n", [NewGeneralState]),
      network(NewState, Blocks);
    {getGeneralState, Sender} -> {GeneralState, _} = State, Sender ! GeneralState,
      %io:format("[network] get general state = ~w...~n", [GeneralState]),
      network(State, Blocks);
    {setNodeState, Sender, NewNodeState} -> {GenState, Map} = State, NewMap = maps:put(Sender, NewNodeState, Map),
      NewState = {GenState, NewMap},
      io:format("[network] set node state of ~w to ~w...~n", [Sender, NewNodeState]),
      network(NewState, Blocks);
    {setNodeStateMineBlock, Sender} -> {_, Map} = State, NewMap = maps:put(Sender, state_mineblock, Map),
      GenNewState = state_mineblock, NewState = {GenNewState, NewMap},
      io:format("[network] set MINE node state of ~w to ~w...~n", [Sender, GenNewState]),
      network(NewState, Blocks);
    {genNewBlock, Sender} ->  io:format("NEW BLOCK # ~w generated by node ~w~n", [Blocks, Sender]), {_, Map} = State,
      GenNewState = state_init, NewState = {GenNewState, Map}, network(NewState, Blocks + 1);
    {reelection, Sender} ->  io:format("REELECTION detected by node ~w~n", [Sender]), {_, Map} = State,
      GenNewState = state_init, NewState = {GenNewState, Map}, network(NewState, Blocks);
    _Other -> network(State, Blocks)
  end.

% random generation in a SGX way
sgx() ->
  io:format("SGX: receiving request to wait...~n"),
  receive
    {give_me_number, Sender} -> Sender ! rand:uniform(3333)
  end,
  sgx().

% questioning of the status of nodes and decision making
poet_check_status(NetworkPid) ->
  NetworkPid ! {getPCount, self()},
  P = receive
    MsgP -> MsgP
  end,
  NetworkPid ! {getNonLeaderCount, self()},
  NL = receive
    MsgNL -> MsgNL
  end,
  NetworkPid ! {getLeaderCount, self()},
  L = receive
    MsgL -> MsgL
  end,
  if
  % condition that P-1 is not a leader (but we are the leader)
    NL == P - 1 -> NetworkPid ! {genNewBlock, self()};
  % number of leaders is not 1 - reelection
    L /= 1  -> NetworkPid ! {reelection, self()};
  % otherwise loop and wait for the status changes of other nodes
    true -> poet_check_status(NetworkPid) % wait for the remaining statuses updates
  end.



poet_node(NetworkPid, SgxPid) ->
  %ждем следующего цикла - состояния STATE_INIT
  NetworkPid ! {getGeneralState, self()},
  receive
    state_init -> ok;
    _ -> poet_node(NetworkPid, SgxPid)
  end,
  NetworkPid ! {setNodeState, self(), state_gen},
  % получить время для ожидания
  SgxPid ! {give_me_number, self()},
  WaitTime = receive
    N -> N
  end,
  % выждать заданное время
  NetworkPid ! {setNodeState, self(), state_waiting},
  io:format("waiting for ~w...~n",[WaitTime]),
  receive
  after WaitTime -> ok
  end,
  NetworkPid ! {getGeneralState, self()},
  receive
  % уже кто-то поставил статус, что он майнит блок, следовательно мы нет
    state_mineblock ->  NetworkPid ! {setNodeState, self(), state_nonmineblock};
    _Other ->
      %еще нету, раз мы первые, то помечаем себя лидером
      NetworkPid ! {setNodeStateMineBlock, self()},
      io:format("status receive start ~n"),
      % опросить состояния других узлов и ждать, пока не установятся в ожидаемые
      poet_check_status(NetworkPid),
      io:format("NEW ROUND INITIATED BY ~w ~n", [self()]),
      % зайти на новый блок, или повторить выборы
      NetworkPid ! {setGeneralState, self(), state_init }
  end,
  poet_node(NetworkPid, SgxPid).

% запуск процессов с повторениями Count
for_spawn(0, _, _) -> ok;
for_spawn(Count, NetworkPid, SgxPid) -> spawn(fun() -> poet_node(NetworkPid, SgxPid) end),
  for_spawn(Count - 1, NetworkPid, SgxPid).

main() ->
  % Запустить 5 процессов-узлов сети, процесс-эмулятор сети и генератор номеров
  for_spawn(5, spawn(fun() -> network({state_init, #{}}, 0) end), spawn(fun() -> sgx() end)).
