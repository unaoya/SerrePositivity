module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FlagSimplex

/-!
概要：path の単体の前に最小の path を加えて旗の解像内に持ち上げる。
方針：最初に始点の一点集合を置き、残りに各 path の前終点集合を置く。
規約：追加した段を除く面で元の path の単体を回収する。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、正規化した評価から元の Hom の作用を回収する。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：path の旗の前に始点の一点集合を加えて正規化した旗にする。
方針：最初の段を始点の一点集合、以後の段を終点を除いた path の集合とする。
規約：元の path の始点を保ち、次数を一つ増やす。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、任意の path の単体を旗の解像に持ち上げる。 -/
noncomputable def pathFlagPrepend {n d : ℕ} {i : Fin (n + 1)}
    (P : Fin (d + 1) ⥤ Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n (d + 1) where
  start := i
  sets := Fin.cons {i} (fun k ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathBeforeLast (P.obj k))
  monotone_sets := by
    classical
    intro a b hab
    induction a using Fin.cases with
    | zero =>
      induction b using Fin.cases with
      | zero => exact le_rfl
      | succ b =>
        intro j hj
        have hji : j = i := Finset.mem_singleton.mp hj
        subst j
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (P.obj b).left⟩
    | succ a =>
      induction b using Fin.cases with
      | zero =>
        change a.succ.val ≤ (0 : Fin (d + 2)).val at hab
        simp only [Fin.val_succ, Fin.val_zero] at hab
        omega
      | succ b =>
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathBeforeLast_mono (P.map (homOfLE (Fin.succ_le_succ_iff.mp hab))).1.1.1
  first := rfl
  lower k j hj := by
    classical
    induction k using Fin.cases with
    | zero => exact (Finset.mem_singleton.mp hj) ▸ le_rfl
    | succ k =>
      exact Fin.castSucc_le_castSucc_iff.mp ((P.obj k).left_le _ (Finset.mem_filter.mp hj).2)

/-- 概要：追加した最初の段を除くと path の正規化した旗を得る。
方針：最初に選んだ段の最大元による切断は path の正規化の定義と一致する。
規約：段を除く写像は Fin.succ の順序埋め込み。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、評価の自然性を適用する面。 -/
lemma pathFlagPrepend_pullback {n d : ℕ} {i : Fin (n + 1)}
    (P : Fin (d + 1) ⥤ Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))) :
    (pathFlagPrepend P).pullback (Fin.succOrderEmb (d + 1)).toOrderHom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathFlagResolution P := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag.ext
  · rfl
  · rfl

/-- 概要：追加した最初の段を除いた path の旗は元の path の単体。
方針：各 path は最後の頂点とそれ以外の点からなることを使う。
規約：単体の添字だけを制限し、始点は移さない。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、評価から元の豊穣 Hom の作用を回収する計算。 -/
lemma pathFlagPrepend_pathFlag {n d : ℕ} {i : Fin (n + 1)}
    (P : Fin (d + 1) ⥤ Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))) :
    (Fin.succOrderEmb (d + 1)).toOrderHom.toFunctor ⋙ (pathFlagPrepend P).pathFlag = P := by
  classical
  apply CategoryTheory.Functor.ext (fun k ↦ ?_)
  apply SimplicialThickening.Path.ext
  apply Set.ext
  intro l
  change (l.down = Fin.last (n + 1) ∨
    ∃ j ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathBeforeLast (P.obj k), l.down = j.castSucc) ↔ l ∈ (P.obj k).I
  constructor
  · rintro (hl | ⟨j, hj, hl⟩)
    · have heq : l = ULift.up (Fin.last (n + 1)) := ULift.ext hl
      rw [heq]
      exact (P.obj k).right
    · have heq : l = ULift.up j.castSucc := ULift.ext hl
      rw [heq]
      exact (Finset.mem_filter.mp hj).2
  · intro hl
    rcases Fin.eq_castSucc_or_eq_last l.down with ⟨j, hj⟩ | hj
    · refine Or.inr ⟨j, ?_, hj⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have heq : l = ULift.up j.castSucc := ULift.ext hj
      rwa [← heq]
    · exact Or.inl hj

/-- 概要：path の正規化後の評価は元の path の Hom の作用を回収する。
方針：先頭に最小の path を加えた旗に評価の自然性を適用し、その面を計算する。
規約：任意の path の始点と任意の次数で成立する。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、pinched 単体側の逆性の非定値な Hom の部分。 -/
lemma coherentPinchedEvaluate_pathFlagResolution {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n d : ℕ}
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y) n)
    {i : Fin (n + 1)}
    (P : Fin (d + 1) ⥤ Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentPinchedEvaluate τ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathFlagResolution P) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentPinchedHom τ i).app (Opposite.op ⦋d⦌) P := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPinchedEvaluate_pullback τ (pathFlagPrepend P)
    (Fin.succOrderEmb (d + 1)).toOrderHom
  rw [pathFlagPrepend_pullback] at h
  have hn := NatTrans.naturality_apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentPinchedHom τ i)
    (SimplexCategory.mkHom (Fin.succOrderEmb (d + 1)).toOrderHom).op
    (pathFlagPrepend P).pathFlag
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentPinchedHom τ i).app (Opposite.op ⦋d⦌)
    ((Fin.succOrderEmb (d + 1)).toOrderHom.toFunctor ⋙ (pathFlagPrepend P).pathFlag) = _ at hn
  rw [pathFlagPrepend_pathFlag] at hn
  exact h.trans hn.symm

/-- 概要：正規化射の後の旗の評価射は元の正規化した Hom の作用。
方針：全次数で path の正規化後の評価の回収則を使う。
規約：単体集合の射の等式として述べる。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、pinched 単体からの変換の回収。 -/
lemma pathResolutionMap_coherentPinchedFlagMap {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y) n)
    (i : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathResolutionMap i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPinchedFlagMap τ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentPinchedHom τ i := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro P
  exact coherentPinchedEvaluate_pathFlagResolution τ P

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
