module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PathPrepend

/-!
概要：先頭面の simplicial thickening は先頭面内の Hom を全て回収する。
方針：castSucc で写した path を、終点以下であることを使って元へ戻す。
規約：追加した最後の頂点を含まない両端点を扱う。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、pinched 単体の先頭面の Hom の回収。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 概要：castSucc の二頂点間の path を元の頂点集合へ戻す。
方針：castSucc による集合の逆像を取り、両端点と上下界を移す。
規約：先頭面の豊穣 Hom の逆写像の対象部分。
使われ方：Kerodon §2.4.3（Tag 00KM）、Corollary 4.6.7.16（Tag 01LQ）、先頭面の Hom の全射性。 -/
def pathFrontInverse {n : ℕ} {i j : Fin (n + 1)}
    (P : Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2))) (ULift.up j.castSucc)) :
    Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j) where
  I := {k | ULift.up k.down.castSucc ∈ P.I}
  left := P.left
  right := P.right
  left_le k hk := Fin.castSucc_le_castSucc_iff.mp (P.left_le _ hk)
  le_right k hk := Fin.castSucc_le_castSucc_iff.mp (P.le_right _ hk)

/-- 概要：先頭面の path の逆写像は包含を保つ関手。
方針：集合の逆像が包含を保つことを使う。
規約：両端点 i,j は元の頂点集合で固定する。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、Hom の nerve の単体を戻す関手。 -/
def pathFrontInverseFunctor {n : ℕ} (i j : Fin (n + 1)) :
    Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2))) (ULift.up j.castSucc) ⥤
      Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j) where
  obj P := pathFrontInverse P
  map f := ⟨⟨⟨fun _ hk ↦ f.1.1.1 hk⟩⟩⟩

/-- 概要：先頭面の path を元に戻して再び埋め込むと同じ path。
方針：全ての点は終点 j.castSucc 以下なので追加した最後の頂点とは異なる。
規約：右逆の関手の等式。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、先頭面の Hom の全射性。 -/
lemma pathFrontInverseFunctor_comp {n : ℕ} (i j : Fin (n + 1)) :
    pathFrontInverseFunctor.{u} i j ⋙ SimplicialThickening.functorMap
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front n).toOrderHom.uliftMap
      (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1)))) ⟨ULift.up j⟩ =
      𝟭 (Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2))) (ULift.up j.castSucc)) := by
  apply CategoryTheory.Functor.ext (fun P ↦ ?_)
  apply SimplicialThickening.Path.ext
  apply Set.ext
  intro k
  change (∃ l : ULift.{u} (Fin (n + 1)),
    ULift.up l.down.castSucc ∈ P.I ∧ ULift.up l.down.castSucc = k) ↔ k ∈ P.I
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact hl
  · intro hk
    have hne : k.down ≠ Fin.last (n + 1) := by
      intro h
      have hle := P.le_right k hk
      change k.down ≤ j.castSucc at hle
      rw [h] at hle
      have hj := j.isLt
      change n + 1 ≤ j.val at hle
      omega
    obtain ⟨l, hl⟩ := Fin.exists_castSucc_eq.mpr hne
    have heq : ULift.up l.castSucc = k := ULift.ext hl
    exact ⟨ULift.up l, heq.symm ▸ hk, heq⟩

/-- 概要：先頭面の豊穣 Hom の作用は各次数で全射。
方針：各 path の単体に逆関手を合成して持ち上げる。
規約：単体集合の epi として表す。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、先頭面の作用の等式を元の Hom に戻す。 -/
instance thickeningFront_map_epi {n : ℕ} (i j : Fin (n + 1)) :
    Epi ((SimplicialThickening.functor (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front n).toOrderHom.uliftMap).map
      (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1)))) ⟨ULift.up j⟩) := by
  rw [NatTrans.epi_iff_epi_app]
  intro d
  rw [epi_iff_surjective]
  intro P
  refine ⟨P ⋙ pathFrontInverseFunctor i j, ?_⟩
  change (P ⋙ pathFrontInverseFunctor i j) ⋙ _ = P
  rw [CategoryTheory.Functor.assoc, pathFrontInverseFunctor_comp]
  rfl

/-- 概要：右 pinched 単体の先頭面内の Hom は全体で豊穣恒等に定値。
方針：先頭面を前に合成した計算から、その作用の epi 性で前合成を消去する。
規約：先頭面内の任意の二頂点を共通の対象 X に正規化する。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、pinched 単体側の逆性の定値な Hom の部分。 -/
lemma coherentPinched_sourceMap_full {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} {n : ℕ}
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y) n)
    (i j : Fin (n + 1)) :
    τ.val.map ⟨ULift.up i.castSucc⟩ ⟨ULift.up j.castSucc⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentPinched_sourceObj τ i) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentPinched_sourceObj τ j)) =
      toUnit _ ≫ eId SSet X := by
  apply (cancel_epi ((SimplicialThickening.functor (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front n).toOrderHom.uliftMap).map
    (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1)))) ⟨ULift.up j⟩)).mp
  calc
    _ = toUnit _ ≫ eId SSet X := by
      simpa only [Category.assoc] using _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPinched_sourceMap τ i j
    _ = _ := by
      apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro P
      rfl

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
