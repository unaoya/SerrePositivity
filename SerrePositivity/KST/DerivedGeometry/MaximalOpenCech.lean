module

public import SerrePositivity.KST.DerivedGeometry.OpenCechContraction

/-!
概要：最大の被覆要素を含む開集合族の Čech 複体を収縮する。
方針：増大の点を最大要素 V とし、その添字を先頭へ挿入する。
規約：族が空間全体を被覆することは要求しない。
使われ方：TT §3、Toën §3.2 の基本開との交叉後の Čech 計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v a b
open CategoryTheory Limits TopologicalSpace
namespace SerrePositivity.KST.DerivedGeometry
variable {X : Type u} [TopologicalSpace X] {ι : Type v}
  (U : ι → Opens X) (V : Opens X) (hU : ∀ i, U i ≤ V)

include hU

/--
概要：V に含まれる開集合族の Čech 対象を V へ増大する。
方針：各交叉から第零成分の射影を通じて V へ送る。
規約：全ての Čech 交叉は非空な添字族の有限積。
使われ方：TT §3、Toën §3.2 の交叉後の Čech 収縮。
-/
def boundedOpenCechAugmented : SimplicialObject.Augmented (FormalCoproduct.{v} (Opens X)) where
  left := (FormalCoproduct.mk ι U).cech
  right := (FormalCoproduct.incl (Opens X)).obj V
  hom :=
    { app := fun _ =>
        { f := fun _ => PUnit.unit
          φ t := Pi.π _ 0 ≫ homOfLE (hU (t 0)) }
      naturality := by
        intros
        exact FormalCoproduct.hom_ext rfl (fun _ => Subsingleton.elim _ _) }

/--
概要：最大要素の添字の先頭挿入は V への増大 Čech 対象の追加退化。
方針：最大要素への各射を第零成分の射影から構成する。
規約：収縮を未証明の存在条件としない。
使われ方：TT §3、Toën §3.2 の基本開局所化後の Čech 収縮。
-/
def maximalOpenCechExtraDegeneracy (j : ι) (hj : U j = V) :
    SimplicialObject.Augmented.ExtraDegeneracy (boundedOpenCechAugmented U V hU) where
  s' :=
    { f := fun _ _ => j
      φ := fun _ => Pi.lift (fun _ => homOfLE (by change V ≤ U j; rw [hj])) }
  s n :=
    { f := fun t => Fin.cons j t
      φ t := Pi.lift (fun a => by
        refine Fin.cases ?_ (fun k => ?_) a
        · exact Pi.π _ 0 ≫ homOfLE (by change U (t 0) ≤ U j; rw [hj]; exact hU _)
        · exact Pi.π _ k) }
  s'_comp_ε := by
    exact FormalCoproduct.hom_ext rfl (fun _ => Subsingleton.elim _ _)
  s₀_comp_δ₁ := by
    refine FormalCoproduct.hom_ext ?_ (fun _ => Subsingleton.elim _ _)
    funext t a
    fin_cases a
    rfl
  s_comp_δ₀ n := by
    refine FormalCoproduct.hom_ext ?_ (fun _ => Subsingleton.elim _ _)
    funext t a
    rfl
  s_comp_δ n i := by
    refine FormalCoproduct.hom_ext ?_ (fun _ => Subsingleton.elim _ _)
    funext t a
    refine Fin.cases ?_ (fun k => ?_) a
    · rfl
    · simp [boundedOpenCechAugmented, SimplicialObject.δ, FormalCoproduct.cech,
        FormalCoproduct.mapPower, SimplexCategory.δ, SimplexCategory.σ]
  s_comp_σ n i := by
    refine FormalCoproduct.hom_ext ?_ (fun _ => Subsingleton.elim _ _)
    funext t a
    refine Fin.cases ?_ (fun k => ?_) a
    · rfl
    · simp [boundedOpenCechAugmented, SimplicialObject.σ, FormalCoproduct.cech,
        FormalCoproduct.mapPower, SimplexCategory.δ, SimplexCategory.σ]

/--
概要：最大要素を含む開集合族の Čech 複体は全正次数で完全。
方針：V への増大の追加退化を評価し、同じ余鎖複体へ収縮を移す。
規約：前層の層条件・被覆の有限性は不要。
使われ方：TT §3、Toën §3.2 の有限基本開被覆の局所化後の計算。
-/
lemma maximalOpenCech_exactAt {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{v} A]
    (P : (Opens X)ᵒᵖ ⥤ A) (j : ι) (hj : U j = V) (n : ℕ) :
    ((cechComplexFunctor U).obj P).ExactAt (n + 1) := by
  let ed := (maximalOpenCechExtraDegeneracy U V hU j hj).map
    (((FormalCoproduct.evalOp (Opens X) A).obj P).rightOp)
  let e := ed.homotopyEquiv
  have h : (AlgebraicTopology.AlternatingFaceMapComplex.obj
      (openCechEvaluation U P).left).ExactAt (n + 1) :=
    (exactAt_iff_of_quasiIsoAt e.hom (n + 1)).mpr
      (ChainComplex.exactAt_succ_single_obj _ n)
  exact (exactAt_iff_of_quasiIsoAt (openCechCochainUnopIso U P).hom (n + 1)).mp h.unop

end SerrePositivity.KST.DerivedGeometry
