module

public import SerrePositivity.KST.NonConnective.DGCountableSum

/-!
概要：元の dg 加群の可算直和に対する、指定した実射による swindle。
方針：零成分と後続成分へ分け、両逆と自然性を元の各直和注入で検証する。
規約：同型の存在を入力せず、元の閉 dg 射そのものを構成する。
使われ方：非可算 κ の dg cone 上の id ⊕ T ≅ T。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.NonConnective
variable (C : Type v) [Category.{u} C] [HasCoproductsOfShape ℕ C] [HasBinaryCoproducts C]

/-- 可算定値族の指定した実余積。 -/
abbrev countableSumObject (M : C) : C := ∐ (fun _ : ℕ ↦ M)

/-- 同じ実余積の標準注入。 -/
abbrev countableSumInjection (M : C) (n : ℕ) : M ⟶ countableSumObject C M :=
  Limits.Sigma.ι (fun _ : ℕ ↦ M) n

/-- 元の実可算直和の、閉 dg 射上の通常の自己関手。 -/
def countableSumOrdinary : C ⥤ C where
  obj := countableSumObject C
  map f := Limits.Sigma.map (fun _ : ℕ ↦ f)
  map_id M := by
    apply Sigma.hom_ext
    intro n
    simp
  map_comp f g := by
    apply Sigma.hom_ext
    intro n
    simp [Category.assoc]

/-- 元の可算直和の後続成分への閉 dg 射。 -/
def countableTail (M : C) :
    countableSumObject C M ⟶ countableSumObject C M :=
  Sigma.desc (fun n : ℕ ↦ countableSumInjection C M (n + 1))

/-- id ⊕ T から T への実際の閉 dg 射。 -/
def countableSwindleHom (M : C) :
    M ⨿ countableSumObject C M ⟶ countableSumObject C M :=
  coprod.desc (countableSumInjection C M 0) (countableTail C M)

/-- T の零成分と後続成分を読み分ける、実際の逆向きの閉 dg 射。 -/
def countableSwindleInv (M : C) :
    countableSumObject C M ⟶ M ⨿ countableSumObject C M :=
  Sigma.desc (fun n : ℕ ↦ match n with
    | 0 => coprod.inl
    | n + 1 => countableSumInjection C M n ≫ coprod.inr)

/-- 同じ指定した二つの閉 dg 射は、実際に両側逆である。 -/
def countableSwindleIso (M : C) :
    M ⨿ countableSumObject C M ≅ countableSumObject C M where
  hom := countableSwindleHom C M
  inv := countableSwindleInv C M
  hom_inv_id := by
    apply coprod.hom_ext
    · simp [countableSwindleHom, countableSwindleInv, countableSumInjection]
    · apply Sigma.hom_ext
      intro n
      simp [countableSwindleHom, countableSwindleInv, countableTail, countableSumInjection]
  inv_hom_id := by
    apply Sigma.hom_ext
    intro n
    cases n with
    | zero => simp [countableSwindleHom, countableSwindleInv, countableSumInjection]
    | succ n =>
      simp [countableSwindleHom, countableSwindleInv, countableTail,
        countableSumInjection, Category.assoc]

/-- 元の id ⊕ T の閉 dg 射上の自己関手。 -/
def countableSwindleSourceOrdinary : C ⥤ C where
  obj M := M ⨿ countableSumObject C M
  map f := coprod.map f ((countableSumOrdinary C).map f)
  map_id M := by
    have h : (countableSumOrdinary C).map (𝟙 M) = 𝟙 (countableSumObject C M) :=
      CategoryTheory.Functor.map_id _ M
    exact (congrArg (coprod.map (𝟙 M)) h).trans coprod.map_id_id
  map_comp f g := by simp only [CategoryTheory.Functor.map_comp, coprod.map_map]

/-- 同じ指定した swindle 射は、全ての元の閉 dg 射について自然。 -/
def countableSwindleOrdinaryIso : countableSwindleSourceOrdinary C ≅ countableSumOrdinary C :=
  NatIso.ofComponents (countableSwindleIso C) (by
    intro M N f
    apply coprod.hom_ext
    · simp [countableSwindleSourceOrdinary, countableSumOrdinary,
        countableSwindleIso, countableSwindleHom,
        countableSumInjection]
    · apply Sigma.hom_ext
      intro n
      simp [countableSwindleSourceOrdinary, countableSumOrdinary,
        countableSwindleIso, countableSwindleHom,
        countableTail, countableSumInjection])

end SerrePositivity.KST.NonConnective
