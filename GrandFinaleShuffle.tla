------------------------- MODULE GrandFinaleShuffle -------------------------

EXTENDS Integers, Sequences, FiniteSets

Cards == {
    "Blank", "Acrobatics", "AcrobaticsPlus", "TacticianPlus", 
    "Reflex", "ReflexPlus", "ExpertisePlus", "PreparedPlus", 
    "ConcentratePlus", "GrandFinale", "CalculatedGamblePlus"
}
MaxHandSize == 10

VARIABLES hand, draw_pile, discard_pile, energy, grand_finale_played

EmptyBag == [c \in Cards |-> 0]

BagSize(b) == 
    b["Blank"] + b["Acrobatics"] + b["AcrobaticsPlus"] + 
    b["TacticianPlus"] + b["Reflex"] + b["ReflexPlus"] + 
    b["ExpertisePlus"] + b["PreparedPlus"] + b["ConcentratePlus"] + 
    b["GrandFinale"] + b["CalculatedGamblePlus"]

AddBags(b1, b2) == [c \in Cards |-> b1[c] + b2[c]]
SubBags(b1, b2) == [c \in Cards |-> b1[c] - b2[c]]

SeqToBag(seq) == 
    [c \in Cards |-> 
        LET indices == {i \in 1..Len(seq) : seq[i] = c}
        IN Cardinality(indices)]

EnergyGainFromBag(bag) == bag["TacticianPlus"] * 2
DrawGainFromBag(bag) == bag["Reflex"] * 2 + bag["ReflexPlus"] * 3

ValidDiscards(b, n) ==
    IF BagSize(b) <= n THEN { b }
    ELSE { sub \in [Cards -> 0..n] : 
             /\ BagSize(sub) = n 
             /\ \A c \in Cards : sub[c] <= b[c] }

\* 生成多重集合的所有全排列序列
PermutationsOfBag(b) ==
    IF BagSize(b) = 0 THEN { <<>> }
    ELSE LET S == BagSize(b)
             Elements == {c \in Cards : b[c] > 0}
         IN { seq \in [1..S -> Elements] :
                \A c \in Elements : 
                  Cardinality({i \in 1..S : seq[i] = c}) = b[c] }

\* 抽牌逻辑，返回可能的结果集合
\* 返回结构：[ drawn: 抽到的序列, rem_dp: 抽后剩余牌库, new_disc: 抽后剩余弃牌堆 ]
DoDraw(dp, disc_pile, n, current_hand_size) ==
    LET allowed == MaxHandSize - current_hand_size
        T == IF n > allowed THEN allowed ELSE n
    IN IF T <= Len(dp) THEN
         \* 牌库够抽，不触发洗牌，返回单一可能性的集合
         { [ drawn |-> SubSeq(dp, 1, T), 
             rem_dp |-> SubSeq(dp, T + 1, Len(dp)), 
             new_disc |-> disc_pile ] }
       ELSE
         \* 触发洗牌
         LET needed == T - Len(dp)
             avail == BagSize(disc_pile)
             actual_extra == IF needed > avail THEN avail ELSE needed
         IN
         \* 遍历所有洗牌可能性，生成状态集合
         { [ drawn |-> dp \o SubSeq(shuffled_dp, 1, actual_extra),
             rem_dp |-> SubSeq(shuffled_dp, actual_extra + 1, avail),
             new_disc |-> EmptyBag ]   \* 弃牌堆被洗空
           : shuffled_dp \in PermutationsOfBag(disc_pile) }

\* 初始状态设定
Init == 
    /\ energy = 3
    /\ grand_finale_played = FALSE
    /\ hand = [EmptyBag EXCEPT !["GrandFinale"]=1, !["Acrobatics"]=1, !["TacticianPlus"]=1]
    /\ draw_pile = <<"ReflexPlus", "Blank", "Blank", "Blank", "Blank">>
    /\ discard_pile = [EmptyBag EXCEPT !["Blank"]=4, !["CalculatedGamblePlus"]=1, !["Reflex"]=1]

\* 卡牌动作实现

PlayGrandFinale ==
    /\ hand["GrandFinale"] > 0
    /\ Len(draw_pile) = 0    
    /\ grand_finale_played' = TRUE  
    /\ UNCHANGED <<hand, energy, discard_pile, draw_pile>>

PlayBlank ==
    /\ hand["Blank"] > 0
    /\ energy >= 1
    /\ hand' = [hand EXCEPT !["Blank"] = @ - 1]
    /\ energy' = energy - 1
    /\ discard_pile' = [discard_pile EXCEPT !["Blank"] = @ + 1]
    /\ UNCHANGED <<draw_pile, grand_finale_played>>

PlayAcro(card_name, draw_amt) ==
    /\ hand[card_name] > 0
    /\ energy >= 1
    /\ LET 
           h1 == [hand EXCEPT ![card_name] = @ - 1]
           e1 == energy - 1
       IN 
           \* 第一段抽牌的所有可能状态
           \E d_res1 \in DoDraw(draw_pile, discard_pile, draw_amt, BagSize(h1)):
               LET h2 == AddBags(h1, SeqToBag(d_res1.drawn))
               IN \E d_bag \in ValidDiscards(h2, 1):
                      LET h3 == SubBags(h2, d_bag)
                          e2 == e1 + EnergyGainFromBag(d_bag)
                          ex_draw == DrawGainFromBag(d_bag)
                      IN 
                          \* 弃牌触发的第二段抽牌的所有可能状态
                          \E d_res2 \in DoDraw(d_res1.rem_dp, d_res1.new_disc, ex_draw, BagSize(h3)):
                              LET h4 == AddBags(h3, SeqToBag(d_res2.drawn))
                              IN
                                  /\ hand' = h4
                                  /\ energy' = e2
                                  /\ draw_pile' = d_res2.rem_dp
                                  \* 结算完毕，刚打出的牌和弃掉的牌进入最终的弃牌堆
                                  /\ discard_pile' = AddBags(d_res2.new_disc, AddBags(d_bag, [EmptyBag EXCEPT ![card_name]=1]))
                                  /\ grand_finale_played' = grand_finale_played

PlayAcrobatics == PlayAcro("Acrobatics", 3)
PlayAcrobaticsPlus == PlayAcro("AcrobaticsPlus", 4)

PlayExpertisePlus ==
    /\ hand["ExpertisePlus"] > 0
    /\ energy >= 1
    /\ LET 
           h1 == [hand EXCEPT !["ExpertisePlus"] = @ - 1]
           e1 == energy - 1
           draw_amt == IF 7 > BagSize(h1) THEN 7 - BagSize(h1) ELSE 0
       IN 
           \E d_res \in DoDraw(draw_pile, discard_pile, draw_amt, BagSize(h1)):
               /\ hand' = AddBags(h1, SeqToBag(d_res.drawn))
               /\ energy' = e1
               /\ draw_pile' = d_res.rem_dp
               /\ discard_pile' = AddBags(d_res.new_disc, [EmptyBag EXCEPT !["ExpertisePlus"]=1])
               /\ grand_finale_played' = grand_finale_played

PlayPreparedPlus ==
    /\ hand["PreparedPlus"] > 0
    /\ LET h1 == [hand EXCEPT !["PreparedPlus"] = @ - 1]
       IN 
           \E d_res1 \in DoDraw(draw_pile, discard_pile, 2, BagSize(h1)):
               LET h2 == AddBags(h1, SeqToBag(d_res1.drawn))
               IN \E d_bag \in ValidDiscards(h2, 2):
                      LET h3 == SubBags(h2, d_bag)
                          e2 == energy + EnergyGainFromBag(d_bag)
                          ex_draw == DrawGainFromBag(d_bag)
                      IN \E d_res2 \in DoDraw(d_res1.rem_dp, d_res1.new_disc, ex_draw, BagSize(h3)):
                             /\ hand' = AddBags(h3, SeqToBag(d_res2.drawn))
                             /\ energy' = e2
                             /\ draw_pile' = d_res2.rem_dp
                             /\ discard_pile' = AddBags(d_res2.new_disc, AddBags(d_bag, [EmptyBag EXCEPT !["PreparedPlus"]=1]))
                             /\ grand_finale_played' = grand_finale_played

PlayConcentratePlus ==
    /\ hand["ConcentratePlus"] > 0
    /\ LET h1 == [hand EXCEPT !["ConcentratePlus"] = @ - 1]
           e1 == energy + 2 
       IN \E d_bag \in ValidDiscards(h1, 2):
              LET h2 == SubBags(h1, d_bag)
                  e2 == e1 + EnergyGainFromBag(d_bag)
                  ex_draw == DrawGainFromBag(d_bag)
              IN \E d_res \in DoDraw(draw_pile, discard_pile, ex_draw, BagSize(h2)):
                     /\ hand' = AddBags(h2, SeqToBag(d_res.drawn))
                     /\ energy' = e2
                     /\ draw_pile' = d_res.rem_dp
                     /\ discard_pile' = AddBags(d_res.new_disc, AddBags(d_bag, [EmptyBag EXCEPT !["ConcentratePlus"]=1]))
                     /\ grand_finale_played' = grand_finale_played

PlayCalculatedGamblePlus ==
    /\ hand["CalculatedGamblePlus"] > 0
    /\ LET h1 == [hand EXCEPT !["CalculatedGamblePlus"] = @ - 1]
           d_bag == h1 
           discard_count == BagSize(d_bag)
           e1 == energy + EnergyGainFromBag(d_bag)
           ex_draw == DrawGainFromBag(d_bag)
           total_draw == discard_count + ex_draw
       IN \E d_res \in DoDraw(draw_pile, discard_pile, total_draw, BagSize(EmptyBag)):
              /\ hand' = AddBags(EmptyBag, SeqToBag(d_res.drawn))
              /\ energy' = e1
              /\ draw_pile' = d_res.rem_dp
              /\ discard_pile' = AddBags(d_res.new_disc, AddBags(d_bag, [EmptyBag EXCEPT !["CalculatedGamblePlus"]=1]))
              /\ grand_finale_played' = grand_finale_played

Stall == 
    /\ UNCHANGED <<hand, draw_pile, discard_pile, energy, grand_finale_played>>

Next == PlayGrandFinale \/ PlayBlank \/ PlayAcrobatics \/ PlayAcrobaticsPlus \/ 
        PlayExpertisePlus \/ PlayPreparedPlus \/ PlayConcentratePlus \/ PlayCalculatedGamblePlus \/ Stall

GameNotWon == ~grand_finale_played

=============================================================================
\* Modification History
\* Last modified Thu Jul 02 22:50:41 CST 2026 by 11319
\* Created Thu Jun 13 20:38:22 CST 2026 by 11319
