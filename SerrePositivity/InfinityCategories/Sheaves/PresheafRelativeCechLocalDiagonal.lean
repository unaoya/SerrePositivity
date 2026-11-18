module

public import SerrePositivity.InfinityCategories.Sheaves.PresheafRelativeCechCoordinates
public import SerrePositivity.InfinityCategories.Sheaves.LocalInjectiveDiagonal
public import Mathlib.Data.Fintype.Lattice

/-!
概要：局所単射な元の前層の相対 Čech 対角は、全ての有限次数で局所全射。
方針：第0座標と各座標の等化篩の有限交叉を使い、同じ全座標の外延性で対角の像へ戻す。
規約：HTT 6.2.2.6 の局所性への通常圏の入力。局所単射から各点の単射を仮定しない。
使われ方：S8 の一般の局所同値を、既証の単射の場合と同じ Čech 解消へ接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {P Q : Cᵒᵖ ⥤ Type u}

/-- 既存の被覆篩の有限交叉の法則を、有限族の inf で読む。 -/
private lemma finiteSieveIntersection_mem (J : GrothendieckTopology C) (U : C)
    {ι : Type*} [Fintype ι] (R : ι → Sieve U) (hR : ∀ i, R i ∈ J U) :
    (⨅ i, R i) ∈ J U := by
  classical
  rw [← Finset.inf_univ_eq_iInf]
  have hs : ∀ s : Finset ι, s.inf R ∈ J U := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using J.top_mem U
    | @insert i s hi ih =>
      rw [Finset.inf_insert]
      exact J.intersection_covering (hR i) ih
  exact hs Finset.univ

/-- 局所単射性だけから、同じ全次数の相対 Čech 対角の局所全射性を得る。 -/
instance relativeCechDiagonal_isLocallySurjective (J : GrothendieckTopology C) (f : P ⟶ Q)
    [CategoryTheory.Presheaf.IsLocallyInjective J f]
    (j : AsSmall.{u} SimplexCategoryᵒᵖ) :
    CategoryTheory.Presheaf.IsLocallySurjective J ((relativeCechDiagonal f).app j) where
  imageSieve_mem {U} q := by
    let n := (AsSmall.down.obj j).unop.len
    let π (i : Fin (n + 1)) := ((relativeCechData f).proj n i).left
    let R (i : Fin (n + 1)) : Sieve U :=
      CategoryTheory.Presheaf.equalizerSieve (F := P) (X := Opposite.op U)
        ((π 0).app (Opposite.op U) q) ((π i).app (Opposite.op U) q)
    have hR : ∀ i, R i ∈ J U := by
      intro i
      apply CategoryTheory.Presheaf.equalizerSieve_mem J f
      exact congrArg (fun η => η.app (Opposite.op U) q)
        ((Over.w ((relativeCechData f).proj n 0)).trans
          (Over.w ((relativeCechData f).proj n i)).symm)
    apply J.superset_covering (S := ⨅ i, R i) ?_ (finiteSieveIntersection_mem J U R hR)
    intro V g hg
    let p := P.map g.op ((π 0).app (Opposite.op U) q)
    refine ⟨p, ?_⟩
    apply presheafRelativeCech_proj_app_ext f n V
    intro i
    have he : P.map g.op ((π 0).app (Opposite.op U) q) =
        P.map g.op ((π i).app (Opposite.op U) q) :=
      (iInf_le R i) g hg
    calc
      _ = p := congrArg (fun η => η.app (Opposite.op V) p)
        (relativeCechDiagonal_proj f j i)
      _ = P.map g.op ((π i).app (Opposite.op U) q) := he
      _ = _ := ((π i).naturality_apply g.op q).symm

end SerrePositivity.InfinityCategories.Sheaves
