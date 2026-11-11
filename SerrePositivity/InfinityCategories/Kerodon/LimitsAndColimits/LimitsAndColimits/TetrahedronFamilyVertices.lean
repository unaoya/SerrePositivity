module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InnerHornFamilyPrescribedVertices
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TetrahedronFamilyFilling

/-!
概要：内ホーン全族の頂点ごとに指定した実充填を、同じ全族へ戻す。
方針：各パラメーター頂点での制限と curry の頂点を照合し、零骨格指定持ち上げを適用する。
規約：元のホーン全族と指定した全ての頂点単体を厳密に回収する。
使われ方：Ind-S (9b) の有限 native Hom 正規化から全族への移行。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 族を同じパラメーター頂点で制限した元の図式。 -/
def familyAtVertex {A K X : SSet.{u}} (F : A ⊗ K ⟶ X) (k : K _⦋0⦌) : A ⟶ X :=
  lift (𝟙 A) (SSet.const k) ≫ F

/-- パラメーター頂点での制限は始域の制限と可換。 -/
lemma familyAtVertex_precomp {A B K X : SSet.{u}} (i : A ⟶ B) (F : B ⊗ K ⟶ X)
    (k : K _⦋0⦌) : familyAtVertex ((i ▷ K) ≫ F) k = i ≫ familyAtVertex F k := by
  simp only [familyAtVertex, ← Category.assoc, lift_whiskerRight, Category.id_comp,
    comp_lift, Category.comp_id, SSet.comp_const]

/-- curry の頂点は同じ族の同じパラメーター頂点での制限を表す。 -/
lemma curry_app_vertex {A K X : SSet.{u}} (F : A ⊗ K ⟶ X) (k : K _⦋0⦌) :
    (curry F).app (Opposite.op ⦋0⦌) k = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (familyAtVertex F k) := by
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  have hα : α = (SimplexCategory.const d.unop ⦋0⦌ 0).op := Subsingleton.elim _ _
  subst α
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 同じ内ホーン全族を保ち、各パラメーター頂点の指定充填を全て厳密回収する。 -/
lemma innerHornFamily_exists_with_vertex_fillers {X : SSet.{u}} [Quasicategory X]
    (n : ℕ) (i : Fin (n + 1)) (hi₀ : 0 < i) (hiₙ : i < Fin.last n)
    (K : SSet.{u}) (F : (Δ[n] : SSet.{u}) ⊗ K ⟶ X)
    (s : K _⦋0⦌ → ((Δ[n] : SSet.{u}) ⟶ X))
    (hs : ∀ k, (horn n i).ι ≫ s k = (horn n i).ι ≫ familyAtVertex F k) :
    ∃ F' : (Δ[n] : SSet.{u}) ⊗ K ⟶ X,
      ((horn n i).ι ▷ K) ≫ F' = ((horn n i).ι ▷ K) ≫ F ∧
      ∀ k, familyAtVertex F' k = s k := by
  let p := (pre (horn n i).ι).app X
  obtain ⟨G, hG, hv⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.innerHornFamily_lift_with_vertices n i hi₀ hiₙ K
    (curry F ≫ p) (fun k => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (s k)) (by
      intro k
      change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((horn n i).ι ≫ s k) = p.app _ ((curry F).app _ k)
      rw [curry_app_vertex, hs]
      rfl)
  refine ⟨uncurry G, ?_, ?_⟩
  · apply curry_injective
    rw [← curry_pre_app, ← curry_pre_app, curry_uncurry]
    exact hG
  · intro k
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective
    rw [← curry_app_vertex, curry_uncurry, hv]

/-- 二つの三単体族が同じ三面を持てば、元の三ホーン全族も厳密に一致する。 -/
lemma tetrahedron_horn_eq_of_faces {X : SSet.{u}} (f g : (Δ[3] : SSet.{u}) ⟶ X)
    (h₀ : stdSimplex.δ (0 : Fin 4) ≫ f = stdSimplex.δ (0 : Fin 4) ≫ g)
    (h₁ : stdSimplex.δ (1 : Fin 4) ≫ f = stdSimplex.δ (1 : Fin 4) ≫ g)
    (h₃ : stdSimplex.δ (3 : Fin 4) ≫ f = stdSimplex.δ (3 : Fin 4) ≫ g) :
    (horn 3 (2 : Fin 4)).ι ≫ f = (horn 3 (2 : Fin 4)).ι ≫ g := by
  apply horn.hom_ext'
  intro j hj
  rw [← Category.assoc, horn.ι_ι, ← Category.assoc, horn.ι_ι]
  fin_cases j
  · exact h₀
  · exact h₁
  · exact False.elim (hj rfl)
  · exact h₃

/-- 定値な単体族を頂点で制限すると、指定の元の単体へ厳密に戻る。 -/
lemma familyAtVertex_constant {A K X : SSet.{u}} (f : A ⟶ X) (k : K _⦋0⦌) :
    familyAtVertex (fst A K ≫ f) k = f := by
  rw [familyAtVertex, ← Category.assoc, lift_fst, Category.id_comp]

/-- 同じ全ホーンの回収から、任意の既知面の全族の回収を得る。 -/
lemma innerHornFamily_face_of_restriction {X K : SSet.{u}} {n : ℕ}
    (i : Fin (n + 2)) (F G : (Δ[n + 1] : SSet.{u}) ⊗ K ⟶ X)
    (h : ((horn (n + 1) i).ι ▷ K) ≫ F = ((horn (n + 1) i).ι ▷ K) ≫ G)
    (j : Fin (n + 2)) (hj : j ≠ i) :
    (stdSimplex.δ j ▷ K) ≫ F = (stdSimplex.δ j ▷ K) ≫ G := by
  have hh := ((horn.ι i j hj) ▷ K) ≫= h
  simpa only [← Category.assoc, ← comp_whiskerRight, horn.ι_ι] using hh

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
