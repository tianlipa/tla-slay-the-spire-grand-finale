--------------------------- MODULE GrandFinale ---------------------------
EXTENDS Integers, Sequences, FiniteSets

Cards == {
    "Blank", "Acrobatics", "AcrobaticsPlus", "TacticianPlus", 
    "Reflex", "ReflexPlus", "ExpertisePlus", "PreparedPlus", 
    "ConcentratePlus", "GrandFinale", "CalculatedGamblePlus"
}

\* 手牌上限
MaxHandSize == 10

VARIABLES hand, draw_pile, discard_pile, energy, reshuffled, grand_finale_played

\* 初始空包
EmptyBag == [c \in Cards |-> 0]

\* 计算手牌总数
HandSize(h) == 
    h["Blank"] + h["Acrobatics"] + h["AcrobaticsPlus"] + 
    h["TacticianPlus"] + h["Reflex"] + h["ReflexPlus"] + 
    h["ExpertisePlus"] + h["PreparedPlus"] + h["ConcentratePlus"] + 
    h["GrandFinale"] + h["CalculatedGamblePlus"]

\* 多重集合的加减法
AddBags(b1, b2) == [c \in Cards |-> b1[c] + b2[c]]
SubBags(b1, b2) == [c \in Cards |-> b1[c] - b2[c]]

\* 辅助函数 序列(牌库)转多重集合(手牌)
SeqToBag(seq) == 
    [c \in Cards |-> 
        LET indices == {i \in 1..Len(seq) : seq[i] = c}
        IN Cardinality(indices)]


EnergyGainFromBag(bag) == bag["TacticianPlus"] * 2
DrawGainFromBag(bag) == bag["Reflex"] * 2 + bag["ReflexPlus"] * 3

\* 生成所有合法的弃牌组合
ValidDiscards(b, n) ==
    IF HandSize(b) <= n THEN { b }
    ELSE { sub \in [Cards -> 0..n] : 
             /\ HandSize(sub) = n 
             /\ \A c \in Cards : sub[c] <= b[c] }

\* 抽牌逻辑
DoDraw(dp, n, current_hand_size) ==
    LET allowed_to_draw == MaxHandSize - current_hand_size
        target_draw == IF n > allowed_to_draw THEN allowed_to_draw ELSE n
    IN IF target_draw > Len(dp)
       THEN [drawn |-> dp, rem |-> <<>>, is_reshuffled |-> TRUE]
       ELSE [drawn |-> SubSeq(dp, 1, target_draw), 
             rem |-> SubSeq(dp, target_draw + 1, Len(dp)), 
             is_reshuffled |-> FALSE]

\* 初始状态设定
Init == 
    /\ energy = 3
    /\ reshuffled = FALSE
    /\ grand_finale_played = FALSE
    \* 初始手牌测试用例配置
    /\ hand = [EmptyBag EXCEPT !["PreparedPlus"] = 1, !["TacticianPlus"] = 1, 
                               !["ExpertisePlus"] = 1, !["Blank"] = 1, !["ConcentratePlus"] = 1]
    /\ discard_pile = EmptyBag
    /\ draw_pile = <<"GrandFinale", "Blank", "Blank", "ReflexPlus", "AcrobaticsPlus", "Blank">>


\* 卡牌动作实现

\* 华丽收场
PlayGrandFinale ==
    /\ ~reshuffled
    /\ hand["GrandFinale"] > 0
    /\ Len(draw_pile) = 0    
    /\ grand_finale_played' = TRUE  
    /\ UNCHANGED <<hand, energy, discard_pile, draw_pile, reshuffled>>

\* 白板
PlayBlank ==
    /\ ~reshuffled
    /\ hand["Blank"] > 0
    /\ energy >= 1
    /\ hand' = [hand EXCEPT !["Blank"] = @ - 1]
    /\ energy' = energy - 1
    /\ discard_pile' = [discard_pile EXCEPT !["Blank"] = @ + 1]
    /\ UNCHANGED <<draw_pile, reshuffled, grand_finale_played>>

\* 杂技
PlayAcro(card_name, draw_amt) ==
    /\ ~reshuffled
    /\ hand[card_name] > 0
    /\ energy >= 1
    /\ LET 
           h1 == [hand EXCEPT ![card_name] = @ - 1]
           e1 == energy - 1
           d_res1 == DoDraw(draw_pile, draw_amt, HandSize(h1))
           h2 == AddBags(h1, SeqToBag(d_res1.drawn))
       IN IF d_res1.is_reshuffled THEN
              /\ reshuffled' = TRUE
              /\ UNCHANGED <<hand, energy, discard_pile, draw_pile, grand_finale_played>>
          ELSE
              \E d_bag \in ValidDiscards(h2, 1):
                  LET h3 == SubBags(h2, d_bag)
                      e2 == e1 + EnergyGainFromBag(d_bag)
                      ex_draw == DrawGainFromBag(d_bag)
                      d_res2 == DoDraw(d_res1.rem, ex_draw, HandSize(h3))
                      h4 == AddBags(h3, SeqToBag(d_res2.drawn))
                  IN IF d_res2.is_reshuffled THEN
                         /\ reshuffled' = TRUE
                         /\ UNCHANGED <<hand, energy, discard_pile, draw_pile, grand_finale_played>>
                     ELSE
                         /\ hand' = h4
                         /\ energy' = e2
                         /\ draw_pile' = d_res2.rem
                         /\ reshuffled' = FALSE
                         /\ discard_pile' = AddBags(discard_pile, AddBags(d_bag, [EmptyBag EXCEPT ![card_name]=1]))
                         /\ grand_finale_played' = grand_finale_played

PlayAcrobatics == PlayAcro("Acrobatics", 3)
PlayAcrobaticsPlus == PlayAcro("AcrobaticsPlus", 4)

\* 独门技术+
PlayExpertisePlus ==
    /\ ~reshuffled
    /\ hand["ExpertisePlus"] > 0
    /\ energy >= 1
    /\ LET 
           h1 == [hand EXCEPT !["ExpertisePlus"] = @ - 1]
           e1 == energy - 1
           draw_amt == IF 7 > HandSize(h1) THEN 7 - HandSize(h1) ELSE 0
           d_res == DoDraw(draw_pile, draw_amt, HandSize(h1))
           h2 == AddBags(h1, SeqToBag(d_res.drawn))
       IN IF d_res.is_reshuffled THEN
              /\ reshuffled' = TRUE
              /\ UNCHANGED <<hand, energy, discard_pile, draw_pile, grand_finale_played>>
          ELSE
              /\ hand' = h2
              /\ energy' = e1
              /\ draw_pile' = d_res.rem
              /\ discard_pile' = [discard_pile EXCEPT !["ExpertisePlus"] = @ + 1]
              /\ reshuffled' = FALSE
              /\ grand_finale_played' = grand_finale_played

\* 早有准备+
PlayPreparedPlus ==
    /\ ~reshuffled
    /\ hand["PreparedPlus"] > 0
    /\ LET 
           h1 == [hand EXCEPT !["PreparedPlus"] = @ - 1]
           d_res1 == DoDraw(draw_pile, 2, HandSize(h1))
           h2 == AddBags(h1, SeqToBag(d_res1.drawn))
       IN IF d_res1.is_reshuffled THEN
              /\ reshuffled' = TRUE
              /\ UNCHANGED <<hand, energy, discard_pile, draw_pile, grand_finale_played>>
          ELSE
              \E d_bag \in ValidDiscards(h2, 2):
                  LET h3 == SubBags(h2, d_bag)
                      e2 == energy + EnergyGainFromBag(d_bag)
                      ex_draw == DrawGainFromBag(d_bag)
                      d_res2 == DoDraw(d_res1.rem, ex_draw, HandSize(h3))
                      h4 == AddBags(h3, SeqToBag(d_res2.drawn))
                  IN IF d_res2.is_reshuffled THEN
                         /\ reshuffled' = TRUE
                         /\ UNCHANGED <<hand, energy, discard_pile, draw_pile, grand_finale_played>>
                     ELSE
                         /\ hand' = h4
                         /\ energy' = e2
                         /\ draw_pile' = d_res2.rem
                         /\ reshuffled' = FALSE
                         /\ discard_pile' = AddBags(discard_pile, AddBags(d_bag, [EmptyBag EXCEPT !["PreparedPlus"]=1]))
                         /\ grand_finale_played' = grand_finale_played

\* 全神贯注+
PlayConcentratePlus ==
    /\ ~reshuffled
    /\ hand["ConcentratePlus"] > 0
    /\ LET 
           h1 == [hand EXCEPT !["ConcentratePlus"] = @ - 1]
           e1 == energy + 2 
       IN 
           \E d_bag \in ValidDiscards(h1, 2):
               LET h2 == SubBags(h1, d_bag)
                   e2 == e1 + EnergyGainFromBag(d_bag)
                   ex_draw == DrawGainFromBag(d_bag)
                   d_res == DoDraw(draw_pile, ex_draw, HandSize(h2))
                   h3 == AddBags(h2, SeqToBag(d_res.drawn))
               IN IF d_res.is_reshuffled THEN
                      /\ reshuffled' = TRUE
                      /\ UNCHANGED <<hand, energy, discard_pile, draw_pile, grand_finale_played>>
                  ELSE
                      /\ hand' = h3
                      /\ energy' = e2
                      /\ draw_pile' = d_res.rem
                      /\ reshuffled' = FALSE
                      /\ discard_pile' = AddBags(discard_pile, AddBags(d_bag, [EmptyBag EXCEPT !["ConcentratePlus"]=1]))
                      /\ grand_finale_played' = grand_finale_played

\* 计算下注+
PlayCalculatedGamblePlus ==
    /\ ~reshuffled
    /\ hand["CalculatedGamblePlus"] > 0
    /\ LET 
           h1 == [hand EXCEPT !["CalculatedGamblePlus"] = @ - 1]
           d_bag == h1 
           discard_count == HandSize(d_bag)
           e1 == energy + EnergyGainFromBag(d_bag)
           ex_draw == DrawGainFromBag(d_bag)
           total_draw == discard_count + ex_draw
           d_res == DoDraw(draw_pile, total_draw, HandSize(EmptyBag))
           h2 == AddBags(EmptyBag, SeqToBag(d_res.drawn))
       IN IF d_res.is_reshuffled THEN
              /\ reshuffled' = TRUE
              /\ UNCHANGED <<hand, energy, discard_pile, draw_pile, grand_finale_played>>
          ELSE
              /\ hand' = h2
              /\ energy' = e1
              /\ draw_pile' = d_res.rem
              /\ reshuffled' = FALSE
              /\ discard_pile' = AddBags(discard_pile, AddBags(d_bag, [EmptyBag EXCEPT !["CalculatedGamblePlus"]=1]))
              /\ grand_finale_played' = grand_finale_played

\* 允许在没有可操作步骤时停止, 防止因为 Deadlock 报错
Stall == 
    /\ UNCHANGED <<hand, draw_pile, discard_pile, energy, reshuffled, grand_finale_played>>

\* 状态转移主函数
Next == PlayGrandFinale \/ PlayBlank \/ PlayAcrobatics \/ PlayAcrobaticsPlus \/ 
        PlayExpertisePlus \/ PlayPreparedPlus \/ PlayConcentratePlus \/ PlayCalculatedGamblePlus \/ Stall

GameNotWon == ~grand_finale_played

=============================================================================
\* Modification History
\* Last modified Thu Jul 02 21:18:04 CST 2026 by 11319
\* Created Thu Jun 06 16:58:32 CST 2026 by 11319