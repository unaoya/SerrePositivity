module
public import SerrePositivity.InfinityCategories.Derived.ContractingElementHomBoundaries

/-! # 終点の収縮による Hom 複体の収縮

概要：収縮対象へ入る Hom 複体の恒等写像を零写像へホモトピックにする。
方針：収縮元との後合成を線形 cochain へ束ね、Leibniz 則から境界が恒等射と示す。
規約：全整数次数で構成する。使われ方：β3 の指定対象への写像空間の収縮。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve CochainComplex HomComplex
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {x y : D}

/-- 終点の収縮元との後合成を次数 −1 の線形 cochain にする。 -/
def contractingTargetHomCochain (h : GradedHom A y y (-1)) :
    Cochain (homObject A D x y) (homObject A D x y) (-1) :=
  Cochain.mk (fun p q hpq => ModuleCat.ofHom ({
    toFun := fun (f : GradedHom A x y p) => (compose A h f (by omega) : GradedHom A x y q)
    map_add' := fun f g => compose_add_right h f g _
    map_smul' := by
      intro a f
      change (p * (-1)).negOnePow •
        ((CategoryTheory.eComp (Complex A) x y y).f q).hom
          ((HomologicalComplex.ιTensorObj (homObject A D x y) (homObject A D y y)
            p (-1) q hpq).hom ((a • f) ⊗ₜ[A] h)) = a • _
      rw [← TensorProduct.smul_tmul', map_smul, map_smul]
      exact smul_comm _ _ _ } : GradedHom A x y p →ₗ[A] GradedHom A x y q))

/-- 後合成による cochain の境界は Hom 複体の恒等射。 -/
lemma contractingTargetHomCochain_differential (h : GradedHom A y y (-1))
    (dh : (homObject A D y y).d (-1) 0 h = (unitElement A y).val) :
    δ (-1) 0 (contractingTargetHomCochain (x := x) h) =
      Cochain.ofHom (𝟙 (homObject A D x y)) := by
  apply Cochain.ext₀
  intro p
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, n + 1 = p := ⟨p - 1, by omega⟩
  rw [δ_v (-1) 0 rfl _ (n + 1) (n + 1) (add_zero _) n ((n + 1) + 1) (by omega) rfl]
  simp only [Int.negOnePow_zero, one_smul]
  apply ConcreteCategory.hom_ext
  intro f
  change differential A (compose A h f (by omega) : GradedHom A x y n) +
    compose A h (differential A f) (by omega) = f
  have dh' : differential A h = (unitElement A y).val := dh
  rw [differential_compose, dh', unit_compose]
  simp [Int.negOnePow_neg, Int.negOnePow_one, Units.smul_def]

/-- Hom 複体の恒等射から零写像への実際の鎖ホモトピー。 -/
def contractingTargetHomotopy (h : GradedHom A y y (-1))
    (dh : (homObject A D y y).d (-1) 0 h = (unitElement A y).val) :
    Homotopy (𝟙 (homObject A D x y)) 0 :=
  DifferentialGraded.contractingHomotopy _ (contractingTargetHomCochain h)
    (contractingTargetHomCochain_differential h dh)

end SerrePositivity.InfinityCategories
