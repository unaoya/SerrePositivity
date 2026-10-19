module

public import SerrePositivity.KST.Spectra.EnrichedParameterCylinderCategory

/-!
概要：順序付きの複数の段を持つ豊穣円柱。
方針：順序の証明を持つ定数単体集合と元の Hom の積を取り、合成では証明を推移させる。
規約：順序の決定可能性も Kan 性も不要。使われ方：零評価の三段の因子分解。
-/

@[expose] public section
noncomputable section
universe u v w
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.EnrichedOrderedCylinder
variable (J : Type w) [Preorder J]

/-- 段の順序の証明を保持する定数単体集合。 -/
def orderWitness (i j : J) : SSet.{u} :=
  (Functor.const SimplexCategoryᵒᵖ).obj (ULift.{u} (PLift (i ≤ j)))

/-- 各段の順序の証明を保持する単体は一意。 -/
instance orderWitness_subsingleton (i j : J) (d : SimplexCategoryᵒᵖ) :
    Subsingleton ((orderWitness J i j : SSet.{u}).obj d) :=
  inferInstanceAs (Subsingleton (ULift.{u} (PLift (i ≤ j))))

/-- 順序の証明と、元の Hom の族の積。 -/
def homByOrder (i j : J) (H : SSet.{u}) : SSet.{u} := orderWitness J i j ⊗ H

/-- 各段に元の豊穣圏の対象を置く。 -/
structure Object (C : Type v) where
  /-- 順序付きの段。 -/
  position : J
  /-- 元の対象。 -/
  val : C

variable {J} {C : Type v} [EnrichedCategory SSet.{u} C]

/-- 順序付き円柱の実際の Hom。 -/
def hom (X Y : Object J C) : SSet.{u} :=
  homByOrder J X.position Y.position (X.val ⟶[SSet] Y.val)

/-- 逆向きの段の Hom の単体は存在しない。 -/
def eliminateHom (X Y : Object J C) (h : ¬ X.position ≤ Y.position) (Z : SSet.{u}) :
    hom X Y ⟶ Z where
  app _ := ↾fun ⟨p, f⟩ ↦ False.elim (h p.down.down)
  naturality {d e} α := by
    apply ConcreteCategory.hom_ext
    rintro ⟨p, f⟩
    exact (h p.down.down).elim

/-- 各段の元の豊穣単位と、反射性の証明。 -/
def identity (X : Object J C) : 𝟙_ SSet.{u} ⟶ hom X X where
  app d := ↾fun _ ↦ (⟨⟨le_rfl⟩⟩, (eId SSet X.val).app d PUnit.unit)
  naturality {d e} α := by
    apply ConcreteCategory.hom_ext
    rintro ⟨⟩
    apply Prod.ext
    · rfl
    · exact ConcreteCategory.congr_hom ((eId SSet X.val).naturality α) PUnit.unit

/-- 順序の証明を推移させ、元の Hom を合成する。 -/
def composition (X Y Z : Object J C) : hom X Y ⊗ hom Y Z ⟶ hom X Z where
  app d := ↾fun ⟨⟨p, f⟩, ⟨q, g⟩⟩ ↦
    (⟨⟨le_trans p.down.down q.down.down⟩⟩, (eComp SSet X.val Y.val Z.val).app d (f, g))
  naturality {d e} α := by
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨p, f⟩, ⟨q, g⟩⟩
    apply Prod.ext
    · rfl
    · let fg : ((X.val ⟶[SSet] Y.val) ⊗ (Y.val ⟶[SSet] Z.val)).obj d := (f, g)
      have h := ConcreteCategory.congr_hom ((eComp SSet X.val Y.val Z.val).naturality α) fg
      exact h

/-- 順序付き円柱の左単位律。 -/
lemma identity_composition (X Y : Object J C) :
    (λ_ (hom X Y)).inv ≫ identity X ▷ hom X Y ≫ composition X X Y = 𝟙 _ := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨p, a⟩
  exact Prod.ext rfl (EnrichedParameterCylinder.base_id_comp_app X.val Y.val d a)

/-- 順序付き円柱の右単位律。 -/
lemma composition_identity (X Y : Object J C) :
    (ρ_ (hom X Y)).inv ≫ hom X Y ◁ identity Y ≫ composition X Y Y = 𝟙 _ := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨p, a⟩
  exact Prod.ext rfl (EnrichedParameterCylinder.base_comp_id_app X.val Y.val d a)

/-- 順序付き円柱の結合律。 -/
lemma composition_assoc (W X Y Z : Object J C) :
    (α_ (hom W X) (hom X Y) (hom Y Z)).inv ≫
      composition W X Y ▷ hom Y Z ≫ composition W Y Z =
      hom W X ◁ composition X Y Z ≫ composition W X Z := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨p, a⟩, ⟨q, b⟩, ⟨r, c⟩⟩
  exact Prod.ext rfl (EnrichedParameterCylinder.base_assoc_app W.val X.val Y.val Z.val d a b c)

/-- 元の Hom と合成から構成した順序付き円柱の豊穣構造。 -/
instance enrichedCategory : EnrichedCategory SSet.{u} (Object J C) where
  Hom := hom
  id := identity
  comp := composition
  id_comp := identity_composition
  comp_id := composition_identity
  assoc := composition_assoc

/-- 豊穣単位からの射による通常の圏構造。 -/
instance category : Category.{u} (Object J C) :=
  inferInstanceAs (Category (ForgetEnrichment SSet.{u} (Object J C)))

/-- 順序付き円柱の実際の単体的圏構造。 -/
instance simplicialCategory : SimplicialCategory (Object J C) where
  homEquiv := Equiv.refl _
  homEquiv_id X := ForgetEnrichment.homTo_id (W := SSet.{u}) (C := Object J C) X
  homEquiv_comp f g := ForgetEnrichment.homTo_comp (W := SSet.{u}) (C := Object J C) f g

end SerrePositivity.KST.Spectra.EnrichedOrderedCylinder
