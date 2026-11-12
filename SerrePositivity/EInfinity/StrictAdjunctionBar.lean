module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ComonadSimplicialResolution
public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.AlgebraicTopology.ExtraDegeneracy

/-!
# 厳密な随伴の bar と忘却後の分裂

概要：HA §4.7.3 の単体的分解の厳密な前段として、任意の随伴の余モナドの bar を取る。
方針：既存の通常の単体圏上の余モナド分解を使い、対象に関する自然性を保つ。
右随伴を適用した後の追加退化は随伴の単位から作る。
規約：モデル構造・cofibrancy・実現の存在や保存は仮定しない。
使われ方：BS-W16 経路 B の厳密な前段。一般圏の補助の移動候補。

verify 待機中の未検証下書き。局所化・実現との比較はここでは作らない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
namespace SerrePositivity.EInfinity.StrictAdjunctionBar
open CategoryTheory Opposite
open SerrePositivity.HomotopyFunctionComplex
open ComonadResolutionOperators
attribute [local implicit_reducible] power ComonadResolutionPresentation.diagram
  ComonadSimplicialResolution.diagram
open scoped Simplicial

section ComonadNaturality
variable {D : Type u₂} [Category.{v₂} D] (G : Comonad D)

/-- 余モナドの反復冪へ対象の射を適用する。 -/
def powerMap {X Y : D} (f : X ⟶ Y) : ∀ n, power G X n ⟶ power G Y n
  | 0 => f
  | n + 1 => G.map (powerMap f n)

@[simp]
lemma powerMap_id (X : D) (n : ℕ) : powerMap G (𝟙 X) n = 𝟙 _ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change G.map (powerMap G (𝟙 X) n) = 𝟙 _
    rw [ih, G.map_id]

@[simp]
lemma powerMap_comp {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    powerMap G (f ≫ g) n = powerMap G f n ≫ powerMap G g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [powerMap, ih, G.map_comp]

/-- 面は、対象に関する反復冪の射と可換。 -/
lemma powerMap_face {X Y : D} (f : X ⟶ Y) (n : ℕ) (i : Fin (n + 1)) :
    powerMap G f (n + 1) ≫ face G Y n i = face G X n i ≫ powerMap G f n := by
  induction n with
  | zero => fin_cases i; exact G.ε.naturality f
  | succ n ih =>
    induction i using Fin.cases with
    | zero => exact G.ε.naturality (powerMap G f (n + 1))
    | succ i =>
      change G.map (powerMap G f (n + 1)) ≫ G.map (face G Y n i) =
        G.map (face G X n i) ≫ G.map (powerMap G f n)
      rw [← G.map_comp, ← G.map_comp, ih]

/-- 退化は、対象に関する反復冪の射と可換。 -/
lemma powerMap_degeneracy {X Y : D} (f : X ⟶ Y) (n : ℕ) (i : Fin (n + 1)) :
    powerMap G f (n + 1) ≫ degeneracy G Y n i =
      degeneracy G X n i ≫ powerMap G f (n + 2) := by
  induction n with
  | zero => fin_cases i; exact G.δ.naturality f
  | succ n ih =>
    induction i using Fin.cases with
    | zero => exact G.δ.naturality (powerMap G f (n + 1))
    | succ i =>
      change G.map (powerMap G f (n + 1)) ≫ G.map (degeneracy G Y n i) =
        G.map (degeneracy G X n i) ≫ G.map (powerMap G f (n + 2))
      rw [← G.map_comp, ← G.map_comp, ih]

/-- 増大も、対象の射と可換。 -/
lemma powerMap_augmentation {X Y : D} (f : X ⟶ Y) (n : ℕ) :
    powerMap G f n ≫ augmentation G Y n = augmentation G X n ≫ f := by
  induction n with
  | zero =>
    change f ≫ 𝟙 Y = 𝟙 X ≫ f
    rw [Category.id_comp, Category.comp_id]
  | succ n ih =>
    change G.map (powerMap G f n) ≫ (G.ε.app _ ≫ augmentation G Y n) = _
    rw [← Category.assoc, G.ε.naturality, CategoryTheory.Functor.id_map, Category.assoc, ih]
    change G.ε.app (power G X n) ≫ (augmentation G X n ≫ f) =
      (G.ε.app (power G X n) ≫ augmentation G X n) ≫ f
    exact (Category.assoc _ _ _).symm

/-- 面と退化の自然性を、表示された単体圏の全射に延ばす。 -/
lemma presentation_naturality {X Y : D} (f : X ⟶ Y)
    {a b : SimplexCategoryGenRel} (θ : a ⟶ b) :
    (ComonadResolutionPresentation.diagram G X).map θ.op ≫ powerMap G f (a.len + 1) =
      powerMap G f (b.len + 1) ≫ (ComonadResolutionPresentation.diagram G Y).map θ.op := by
  induction θ using SimplexCategoryGenRel.hom_induction with
  | id =>
    rw [op_id, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  | @comp_δ n m θ i ih =>
    simp only [op_comp, CategoryTheory.Functor.map_comp, Category.assoc]
    rw [ih]
    simp only [SimplexCategoryGenRel.mk_len]
    rw [← Category.assoc, ComonadResolutionPresentation.diagram_face,
      ← powerMap_face G f (m + 1) i, Category.assoc, ComonadResolutionPresentation.diagram_face]
  | @comp_σ n m θ i ih =>
    simp only [op_comp, CategoryTheory.Functor.map_comp, Category.assoc]
    rw [ih]
    simp only [SimplexCategoryGenRel.mk_len]
    rw [← Category.assoc, ComonadResolutionPresentation.diagram_degeneracy,
      ← powerMap_degeneracy G f m i, Category.assoc,
      ComonadResolutionPresentation.diagram_degeneracy]

/-- 対象の射が誘導する、通常の単体圏上の bar の射。 -/
def diagramMap {X Y : D} (f : X ⟶ Y) :
    ComonadSimplicialResolution.diagram G X ⟶ ComonadSimplicialResolution.diagram G Y where
  app n := powerMap G f (n.unop.len + 1)
  naturality {_n _m} θ :=
    presentation_naturality G f (SerrePositivity.SimplexPresentation.inverse.map θ.unop)

/-- 余モナドの bar を対象の全関手として保つ。 -/
def diagramFunctor : D ⥤ SimplicialObject D where
  obj := ComonadSimplicialResolution.diagram G
  map f := diagramMap G f
  map_id X := by ext n; exact powerMap_id G X _
  map_comp f g := by ext n; exact powerMap_comp G f g _

/-- 通常の単体圏上の、既存の増大を伴う bar。 -/
def augmented (X : D) : SimplicialObject.Augmented D where
  left := ComonadSimplicialResolution.diagram G X
  right := X
  hom := ComonadSimplicialResolution.augmentation G X

/-- 増大も対象の射とともに運ぶ。 -/
def augmentedFunctor : D ⥤ SimplicialObject.Augmented D where
  obj := augmented G
  map f :=
    { left := diagramMap G f
      right := f
      w := by
        ext n
        exact powerMap_augmentation G f (n.unop.len + 1) }
  map_id X := by
    apply SimplicialObject.Augmented.hom_ext
    · exact (diagramFunctor G).map_id X
    · rfl
  map_comp f g := by
    apply SimplicialObject.Augmented.hom_ext
    · exact (diagramFunctor G).map_comp f g
    · rfl

end ComonadNaturality

section AdjunctionSplit
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {U : D ⥤ C} (h : F ⊣ U)

/-- 随伴の実際の余モナドに対する bar の全関手。 -/
abbrev barFunctor : D ⥤ SimplicialObject D := diagramFunctor h.toComonad

/-- 随伴の bar と増大を束ねた全関手。 -/
abbrev barAugmentedFunctor : D ⥤ SimplicialObject.Augmented D :=
  augmentedFunctor h.toComonad

/-- 右随伴を適用した後の bar と増大。定値関手の合成の比較を成分で明示する。 -/
def underlyingAugmented (X : D) : SimplicialObject.Augmented C where
  left := ComonadSimplicialResolution.diagram h.toComonad X ⋙ U
  right := U.obj X
  hom :=
    { app n := U.map ((ComonadSimplicialResolution.augmentation h.toComonad X).app n)
      naturality {n m} θ := by
        change U.map ((ComonadSimplicialResolution.diagram h.toComonad X).map θ) ≫
          U.map ((ComonadSimplicialResolution.augmentation h.toComonad X).app m) =
            U.map ((ComonadSimplicialResolution.augmentation h.toComonad X).app n) ≫ 𝟙 _
        rw [Category.comp_id, ← U.map_comp]
        apply congrArg U.map
        have ht := (ComonadSimplicialResolution.augmentation h.toComonad X).naturality θ
        change _ = (ComonadSimplicialResolution.augmentation h.toComonad X).app n ≫ 𝟙 X at ht
        exact ht.trans (Category.comp_id _) }


/-- 忘却後の追加退化。代数側の分裂は要求しない。 -/
def underlyingExtraDegeneracy (X : D) :
    SimplicialObject.Augmented.ExtraDegeneracy (underlyingAugmented h X) where
  s' := h.unit.app (U.obj X)
  s n := h.unit.app (U.obj (power h.toComonad X (n + 1)))
  s'_comp_ε := by
    change h.unit.app (U.obj X) ≫ U.map (h.counit.app X ≫ 𝟙 X) = 𝟙 _
    have hc : h.counit.app X ≫ 𝟙 X = h.counit.app X := Category.comp_id _
    exact (congrArg (fun k => h.unit.app (U.obj X) ≫ U.map k) hc).trans
      (h.right_triangle_components X)
  s₀_comp_δ₁ := by
    change h.unit.app (U.obj (h.toComonad.obj X)) ≫
      U.map ((ComonadSimplicialResolution.diagram h.toComonad X).δ (1 : Fin 2)) = _
    rw [ComonadSimplicialResolution.diagram_face]
    change h.unit.app (U.obj (h.toComonad.obj X)) ≫
      U.map (face h.toComonad X 1 (0 : Fin 1).succ) =
        U.map (h.counit.app X ≫ 𝟙 X) ≫ h.unit.app (U.obj X)
    rw [face_succ, face_zero]
    have hc : h.counit.app X ≫ 𝟙 X = h.counit.app X := Category.comp_id _
    rw [hc]
    change h.unit.app (U.obj (h.toComonad.obj X)) ≫
      U.map (F.map (U.map (h.counit.app X))) =
        U.map (h.counit.app X) ≫ h.unit.app (U.obj X)
    exact (h.unit.naturality (U.map (h.counit.app X))).symm
  s_comp_δ₀ n := by
    change h.unit.app (U.obj (power h.toComonad X (n + 1))) ≫
      U.map ((ComonadSimplicialResolution.diagram h.toComonad X).δ (0 : Fin (n + 2))) = _
    rw [ComonadSimplicialResolution.diagram_face, face_zero]
    change h.unit.app (U.obj (power h.toComonad X (n + 1))) ≫
      U.map (h.counit.app (power h.toComonad X (n + 1))) = 𝟙 _
    exact h.right_triangle_components _
  s_comp_δ n i := by
    change h.unit.app (U.obj (power h.toComonad X (n + 2))) ≫
      U.map ((ComonadSimplicialResolution.diagram h.toComonad X).δ i.succ) =
        U.map ((ComonadSimplicialResolution.diagram h.toComonad X).δ i) ≫
          h.unit.app (U.obj (power h.toComonad X (n + 1)))
    rw [ComonadSimplicialResolution.diagram_face, ComonadSimplicialResolution.diagram_face]
    change h.unit.app (U.obj (power h.toComonad X (n + 2))) ≫
      U.map (F.map (U.map (face h.toComonad X (n + 1) i))) =
        U.map (face h.toComonad X (n + 1) i) ≫
          h.unit.app (U.obj (power h.toComonad X (n + 1)))
    exact (h.unit.naturality (U.map (face h.toComonad X (n + 1) i))).symm
  s_comp_σ n i := by
    change h.unit.app (U.obj (power h.toComonad X (n + 1))) ≫
      U.map ((ComonadSimplicialResolution.diagram h.toComonad X).σ i.succ) =
        U.map ((ComonadSimplicialResolution.diagram h.toComonad X).σ i) ≫
          h.unit.app (U.obj (power h.toComonad X (n + 2)))
    rw [ComonadSimplicialResolution.diagram_degeneracy,
      ComonadSimplicialResolution.diagram_degeneracy]
    change h.unit.app (U.obj (power h.toComonad X (n + 1))) ≫
      U.map (F.map (U.map (degeneracy h.toComonad X n i))) =
        U.map (degeneracy h.toComonad X n i) ≫
          h.unit.app (U.obj (power h.toComonad X (n + 2)))
    exact (h.unit.naturality (U.map (degeneracy h.toComonad X n i))).symm

/-- 忘却後の増大の分裂から得られる、定値図式への自然な切断。 -/
def underlyingSection (X : D) :
    (SimplicialObject.const C).obj (U.obj X) ⟶ (underlyingAugmented h X).left :=
  (underlyingExtraDegeneracy h X).section_

/-- その切断は、忘却後の同じ増大の右逆である。 -/
lemma underlyingSection_comp_augmentation (X : D) :
    underlyingSection h X ≫ (underlyingAugmented h X).hom = 𝟙 _ :=
  (underlyingExtraDegeneracy h X).section_comp_hom

/-- 追加退化の対象についての自然性。 -/
lemma underlyingExtraDegeneracy_naturality {X Y : D} (f : X ⟶ Y) (n : ℕ) :
    U.map (powerMap h.toComonad f (n + 1)) ≫
        (underlyingExtraDegeneracy h Y).s n =
      (underlyingExtraDegeneracy h X).s n ≫
        U.map (powerMap h.toComonad f (n + 2)) :=
  h.unit.naturality (U.map (powerMap h.toComonad f (n + 1)))

/-- 零次の切断も対象について自然。 -/
lemma underlyingExtraDegeneracy_section_naturality {X Y : D} (f : X ⟶ Y) :
    U.map f ≫ (underlyingExtraDegeneracy h Y).s' =
      (underlyingExtraDegeneracy h X).s' ≫ U.map (powerMap h.toComonad f 1) :=
  h.unit.naturality (U.map f)

end AdjunctionSplit
end SerrePositivity.EInfinity.StrictAdjunctionBar
