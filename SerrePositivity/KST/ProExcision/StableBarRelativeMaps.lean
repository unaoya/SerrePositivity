module
public import SerrePositivity.KST.ProExcision.StableBarHomologyComparison
public import SerrePositivity.KST.ProExcision.RelativeModuleColimitNaturality

/-!
# 実安定 bar の相対写像と有限 rank の実商図式

概要：実単体的モノイド図式の正方形を安定相対写像と有限相対自然変換へ移す。
方針：実 bar・借用 H_*・実余極限の関手性を合成する。
規約：KST Proposition 4.14、SW92 Lemma 1.4。使われ方：安定相対零化の実比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Limits Comparison
variable {A B A' B' : ℕ ⥤ SimplicialObject MonCat.{u}}
variable {s : A ⟶ B} {s' : A' ⟶ B'}

/-- 概要：実モノイド図式の正方形が実安定相対 bar に誘導する写像。
方針：実余極限・実 bar・借用関手を正方形へ適用し、実相対商へ降ろす。
規約：SW92 Lemma 1.4。使われ方：実安定相対自己写像。 -/
def relativeStableBarMap (F : SSet.{u} ⥤ ModuleCat.{u} ℤ)
    (a : A ⟶ A') (b : B ⟶ B') (h : s ≫ b = a ≫ s') :
    relativeModule (F.map (monoidBarMap (colimMap s))) ⟶
      relativeModule (F.map (monoidBarMap (colimMap s'))) :=
  relativeModuleMap _ _ (F.map (monoidBarMap (colimMap a)))
    (F.map (monoidBarMap (colimMap b))) (by
      rw [← F.map_comp, ← F.map_comp, ← monoidBarMap_comp, ← monoidBarMap_comp]
      change F.map (monoidBarMap (colim.map s ≫ colim.map b)) =
        F.map (monoidBarMap (colim.map a ≫ colim.map s'))
      rw [← colim.map_comp, ← colim.map_comp, h])

/-- 概要：実モノイド図式の正方形は有限 rank の実 H_* の正方形を与える。
方針：実 bar と借用関手の後合成を正方形に適用する。
規約：KST Proposition 4.14。使われ方：実有限相対図式の写像。 -/
lemma finiteBarHomologySquare (F : SSet.{u} ⥤ ModuleCat.{u} ℤ)
    (a : A ⟶ A') (b : B ⟶ B') (h : s ≫ b = a ≫ s') :
    Functor.whiskerRight s (monoidBarFunctor ⋙ F) ≫
        Functor.whiskerRight b (monoidBarFunctor ⋙ F) =
      Functor.whiskerRight a (monoidBarFunctor ⋙ F) ≫
        Functor.whiskerRight s' (monoidBarFunctor ⋙ F) := by
  rw [← Functor.whiskerRight_comp, ← Functor.whiskerRight_comp, h]

/-- 概要：実安定相対 bar 比較は実モノイド図式の正方形に自然。
方針：実相対同型の合成則、実 bar ホモロジー比較の自然性、実商余極限の自然性を使う。
規約：KST Proposition 4.14、SW92 Lemma 1.4。
使われ方：有限 rank の実相対零化を実安定相対写像へ移す。 -/
lemma SimplicialHomologyModel.relativeBarSequentialColimitIso_natural
    {F : SSet.{u} ⥤ ModuleCat.{u} ℤ} {i : ℕ} (M : SimplicialHomologyModel F i)
    (a : A ⟶ A') (b : B ⟶ B') (h : s ≫ b = a ≫ s') :
    relativeStableBarMap F a b h ≫ (M.relativeBarSequentialColimitIso s').hom =
      (M.relativeBarSequentialColimitIso s).hom ≫
        colimMap (relativeModuleDiagramMap (Functor.whiskerRight a (monoidBarFunctor ⋙ F))
          (Functor.whiskerRight b (monoidBarFunctor ⋙ F)) (finiteBarHomologySquare F a b h)) := by
  let e := relativeModuleIso _ _ (M.barSequentialColimitIso A) (M.barSequentialColimitIso B)
    (M.barSequentialColimitIso_natural s)
  let e' := relativeModuleIso _ _ (M.barSequentialColimitIso A') (M.barSequentialColimitIso B')
    (M.barSequentialColimitIso_natural s')
  have hn : relativeStableBarMap F a b h ≫ e'.hom =
      e.hom ≫ relativeModuleSequentialMap (Functor.whiskerRight a (monoidBarFunctor ⋙ F))
        (Functor.whiskerRight b (monoidBarFunctor ⋙ F)) (finiteBarHomologySquare F a b h) := by
    dsimp only [e, e', relativeModuleIso, relativeStableBarMap, relativeModuleSequentialMap]
    rw [relativeModuleMap_comp, relativeModuleMap_comp]
    apply relativeModuleMap_eq_of_right_eq
    exact M.barSequentialColimitIso_natural b
  change relativeStableBarMap F a b h ≫ (e'.hom ≫ _) = (e.hom ≫ _) ≫ _
  rw [← Category.assoc, hn, Category.assoc, relativeModuleSequentialColimitIso_natural,
    ← Category.assoc]

end SerrePositivity.KST.ProExcision
