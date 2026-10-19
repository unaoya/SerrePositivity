module
public import SerrePositivity.InfinityCategories.Derived.ContractingElementHomBoundaries

/-! # 始点の収縮による Hom 複体の収縮

概要：収縮対象から出る Hom 複体の恒等写像を零写像へホモトピックにする。
方針：豊穣順の前合成を線形 cochain とし、Leibniz 則と単位則を使う。
規約：通常順の合成での次数符号を豊穣順に吸収する。使われ方：β3 の写像空間の収縮。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve CochainComplex HomComplex
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {x y : D}

/-- 始点の収縮元との前合成を次数 −1 の線形 cochain にする。 -/
def contractingSourceHomCochain (h : GradedHom A x x (-1)) :
    Cochain (homObject A D x y) (homObject A D x y) (-1) :=
  Cochain.mk (fun p q hpq => ModuleCat.ofHom ({
    toFun := fun (f : GradedHom A x y p) => (forward A h f (by omega) : GradedHom A x y q)
    map_add' := by
      intro f g
      simp [forward, TensorProduct.tmul_add]
    map_smul' := by
      intro a f
      change ((CategoryTheory.eComp (Complex A) x x y).f q).hom
        ((HomologicalComplex.ιTensorObj (homObject A D x x) (homObject A D x y)
          (-1) p q (by omega)).hom (h ⊗ₜ[A] (a • f))) = a • _
      rw [TensorProduct.tmul_smul, map_smul, map_smul]
      rfl } : GradedHom A x y p →ₗ[A] GradedHom A x y q))

/-- 前合成による cochain の境界は Hom 複体の恒等射。 -/
lemma contractingSourceHomCochain_differential (h : GradedHom A x x (-1))
    (dh : (homObject A D x x).d (-1) 0 h = (unitElement A x).val) :
    δ (-1) 0 (contractingSourceHomCochain (y := y) h) =
      Cochain.ofHom (𝟙 (homObject A D x y)) := by
  apply Cochain.ext₀
  intro p
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, n + 1 = p := ⟨p - 1, by omega⟩
  rw [δ_v (-1) 0 rfl _ (n + 1) (n + 1) (add_zero _) n ((n + 1) + 1) (by omega) rfl]
  simp only [Int.negOnePow_zero, one_smul]
  apply ConcreteCategory.hom_ext
  intro f
  change differential A (forward A h f (by omega) : GradedHom A x y n) +
    forward A h (differential A f) (by omega) = f
  have dh' : differential A h = (unitElement A x).val := dh
  rw [differential_forward, dh', forward_unit]
  simp [Int.negOnePow_neg, Int.negOnePow_one, Units.smul_def]

/-- 出ていく Hom 複体の恒等射から零写像への鎖ホモトピー。 -/
def contractingSourceHomotopy (h : GradedHom A x x (-1))
    (dh : (homObject A D x x).d (-1) 0 h = (unitElement A x).val) :
    Homotopy (𝟙 (homObject A D x y)) 0 :=
  DifferentialGraded.contractingHomotopy _ (contractingSourceHomCochain h)
    (contractingSourceHomCochain_differential h dh)

end SerrePositivity.InfinityCategories
