module

public import SerrePositivity.EInfinity.Hammock.ForwardPathPullback

/-!
# 終点を動かす元の forward 射列の pullback の関手性

概要：元の射列・終点置換・その可換四角形を全て動かして pullback 射列を比較する。
方針：各頂点の元の pullback.map と二つの射影で恒等・合成と自然性を検査する。
規約：元の終点は固定しない。比較は元の全頂点と全射に自然。
使われ方：モデル圏の関手的分解から長い forward ブロックへの同時置換。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.ForwardPath
open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {n : ℕ}

omit [HasPullbacks C] in
lemma terminalLeg_comparison {F G : ComposableArrows C n} (η : F ⟶ G) (i : Fin (n + 1)) :
    terminalLeg F i ≫ η.app (Fin.last n) = η.app i ≫ terminalLeg G i :=
  η.naturality (homOfLE (Fin.le_last i))

variable {s t r : TerminalReplacement C n} (m : s ⟶ t)

def pullbackComparisonApp (i : Fin (n + 1)) : pullbackObj s i ⟶ pullbackObj t i :=
  pullback.map (terminalLeg s.right i) s.hom (terminalLeg t.right i) t.hom
    (m.right.app i) m.left (m.right.app (Fin.last n)) (terminalLeg_comparison m.right i)
    m.w.symm

lemma pullbackComparisonApp_fst (i : Fin (n + 1)) :
    pullbackComparisonApp m i ≫ pullback.fst (terminalLeg t.right i) t.hom =
      pullback.fst (terminalLeg s.right i) s.hom ≫ m.right.app i := pullback.lift_fst _ _ _

lemma pullbackComparisonApp_snd (i : Fin (n + 1)) :
    pullbackComparisonApp m i ≫ pullback.snd (terminalLeg t.right i) t.hom =
      pullback.snd (terminalLeg s.right i) s.hom ≫ m.left := pullback.lift_snd _ _ _

lemma pullbackComparisonApp_naturality {i j : Fin (n + 1)} (f : i ⟶ j) :
    pullbackArrow s f ≫ pullbackComparisonApp m j =
      pullbackComparisonApp m i ≫ pullbackArrow t f := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackComparisonApp_fst, ← Category.assoc, pullbackArrow_fst,
      Category.assoc, Category.assoc, pullbackArrow_fst,
      ← Category.assoc (pullbackComparisonApp m i),
      pullbackComparisonApp_fst, Category.assoc, m.right.naturality f]
  · rw [Category.assoc, pullbackComparisonApp_snd, ← Category.assoc, pullbackArrow_snd,
      Category.assoc, pullbackArrow_snd, pullbackComparisonApp_snd]

def pullbackComparison : pullbackPath s ⟶ pullbackPath t where
  app := pullbackComparisonApp m
  naturality _ _ f := pullbackComparisonApp_naturality m f

def pullbackFunctor : TerminalReplacement C n ⥤ ComposableArrows C n where
  obj := pullbackPath
  map := pullbackComparison
  map_id s := by
    apply NatTrans.ext
    funext i
    apply pullback.hom_ext
    · change pullbackComparisonApp (𝟙 s) i ≫ _ = (𝟙 _) ≫ _
      rw [pullbackComparisonApp_fst]
      simp
    · change pullbackComparisonApp (𝟙 s) i ≫ _ = (𝟙 _) ≫ _
      rw [pullbackComparisonApp_snd]
      simp
  map_comp m k := by
    apply NatTrans.ext
    funext i
    apply pullback.hom_ext
    · change pullbackComparisonApp (m ≫ k) i ≫ _ =
        (pullbackComparisonApp m i ≫ pullbackComparisonApp k i) ≫ _
      rw [pullbackComparisonApp_fst, Category.assoc, pullbackComparisonApp_fst,
        ← Category.assoc, pullbackComparisonApp_fst, Category.assoc]
      rfl
    · change pullbackComparisonApp (m ≫ k) i ≫ _ =
        (pullbackComparisonApp m i ≫ pullbackComparisonApp k i) ≫ _
      rw [pullbackComparisonApp_snd, Category.assoc, pullbackComparisonApp_snd,
        ← Category.assoc, pullbackComparisonApp_snd, Category.assoc]
      rfl

end SerrePositivity.EInfinity.Hammock.ForwardPath
