module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RetractChainFamily

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeTransferredFamilies
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarChainFamily

/-!
# 中断した任意モデル源への一般化：OrdinaryBarFreeChainTransfer

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Transfer arbitrary finite chains of actual free-resolution arrows。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0173][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0173
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Transfer arbitrary finite chains of actual free-resolution arrows

An arbitrary whole parameter may map to the simplex parameter. Each chain
junction has its own contraction parameter. Zero and one faces retain any
prefix and suffix; the empty and singleton chains have the expected values.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeChainTransfer
open FreeGeneratorCategories OrdinaryBarFreeResolutionSeed OrdinaryBarChoiceBoundaryGluing
open OrdinaryBarRetractSystem
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v}) (n : ℕ)

abbrev chain (U : SSet.{max u v}) (X Y : D C) := OrdinaryBarChainFamily.chain hcof hfib U X Y

variable {U V : SSet.{max u v}} (j : U ⟶ parameters P n)

def snoc {a : D C} {X Y : degree (D C) (n + 1)} (q : chain hcof hfib U a X)
    (f : X ⟶ Y) (t : U ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval) : chain hcof hfib U a Y :=
  q.familySnoc (ParameterComposition.substitute j
    (OrdinaryBarFreeAmbientFamilies.family hcof hfib P n f)) t

lemma snoc_substitute (k : V ⟶ U) {a : D C} {X Y : degree (D C) (n + 1)}
    (q : chain hcof hfib U a X) (f : X ⟶ Y) (t : U ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval) :
    (snoc hcof hfib P n j q f t).substitute k =
      snoc hcof hfib P n (k ≫ j) (q.substitute k) f (k ≫ t) := by
  simp only [snoc, RetractChainFamily.Chain.substitute, ParameterComposition.substitute,
    whiskerLeft_comp, Category.assoc]

def ofPath {X : degree (D C) (n + 1)} :
    {Y : degree (D C) (n + 1)} → Quiver.Path X Y →
      (ℕ → (U ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval)) → chain hcof hfib U X Y
  | _, .nil, _ => .nil
  | _, .cons q f, t => snoc hcof hfib P n j (ofPath q t) f (t q.length)

lemma ofPath_length {X Y : degree (D C) (n + 1)} (q : Quiver.Path X Y)
    (t : ℕ → (U ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval)) :
    (ofPath hcof hfib P n j q t).length = q.length := by
  induction q with
  | nil => rfl
  | cons q f ih => change (ofPath hcof hfib P n j q t).length + 1 = q.length + 1; rw [ih]

lemma ofPath_substitute (k : V ⟶ U) {X Y : degree (D C) (n + 1)} (q : Quiver.Path X Y)
    (t : ℕ → (U ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval)) :
    (ofPath hcof hfib P n j q t).substitute k =
      ofPath hcof hfib P n (k ≫ j) q (fun r => k ≫ t r) := by
  induction q with
  | nil => rfl
  | cons q f ih => simp only [ofPath, snoc_substitute, ih]

def family {X Y : degree (D C) (n + 1)} (q : Quiver.Path X Y)
    (t : ℕ → (U ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval)) : lifted hcof hfib X ⊗ U ⟶ lifted hcof hfib Y :=
  OrdinaryBarChainFamily.family hcof hfib (ofPath hcof hfib P n j q t)

lemma family_substitute (k : V ⟶ U) {X Y : degree (D C) (n + 1)} (q : Quiver.Path X Y)
    (t : ℕ → (U ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval)) :
    family hcof hfib P n (k ≫ j) q (fun r => k ≫ t r) =
      ParameterComposition.substitute k (family hcof hfib P n j q t) := by
  rw [family, ← ofPath_substitute, OrdinaryBarChainFamily.family_substitute]
  rfl

lemma family_nil (X : degree (D C) (n + 1)) (t : ℕ → (U ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval)) :
    family hcof hfib P n j (Quiver.Path.nil : Quiver.Path X X) t = fst (lifted hcof hfib X) U := by
  ext m x
  exact types_congr_hom (congr_app (section_fac hcof hfib X) m) x.1

lemma family_single {X Y : degree (D C) (n + 1)} (f : X ⟶ Y)
    (t : ℕ → (U ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval)) :
    family hcof hfib P n j f.toPath t =
      OrdinaryBarFreeTransferredFamilies.ofFamily hcof hfib (ParameterComposition.substitute j
        (OrdinaryBarFreeAmbientFamilies.family hcof hfib P n f)) := by
  refine (RetractChainFamily.transfer_last_family_parameter (ambient hcof hfib) (lifted hcof hfib)
    (section_ hcof hfib) (projection hcof hfib) (contraction hcof hfib)
    (contraction_over hcof hfib) (.nil : chain hcof hfib U X X)
    (ParameterComposition.substitute j (OrdinaryBarFreeAmbientFamilies.family hcof hfib P n f))
    (t 0)).trans ?_
  ext m x
  rfl

lemma zero_face {a d : D C} {X Y Z : degree (D C) (n + 1)}
    (q : chain hcof hfib U a X) (f : X ⟶ Y) (g : Y ⟶ Z)
    (t : U ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval) (r : chain hcof hfib U Z d) :
    OrdinaryBarChainFamily.family hcof hfib
      ((snoc hcof hfib P n j (snoc hcof hfib P n j q f (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.zero U)) g t).append r) =
    OrdinaryBarChainFamily.family hcof hfib ((snoc hcof hfib P n j q (f ≫ g) t).append r) := by
  have hh := RetractChainFamily.zero_family_face (ambient hcof hfib) (lifted hcof hfib)
    (section_ hcof hfib) (projection hcof hfib) (contraction hcof hfib) q
    (ParameterComposition.substitute j (OrdinaryBarFreeAmbientFamilies.family hcof hfib P n f))
    (ParameterComposition.substitute j (OrdinaryBarFreeAmbientFamilies.family hcof hfib P n g)) t r
  simpa only [snoc, OrdinaryBarChainFamily.family, OrdinaryBarFreeAmbientFamilies.family_comp,
    ParameterComposition.substitute_comp] using hh

lemma one_face {a d : D C} {X Y : degree (D C) (n + 1)}
    (q : chain hcof hfib U a X) (f : X ⟶ Y) (r : chain hcof hfib U Y d) :
    OrdinaryBarChainFamily.family hcof hfib
      ((snoc hcof hfib P n j q f (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.one U)).append r) =
    ParameterComposition.comp
      (OrdinaryBarChainFamily.family hcof hfib
        (snoc hcof hfib P n j q f (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.zero U)))
      (OrdinaryBarChainFamily.family hcof hfib r) :=
  RetractChainFamily.one_family_face _ _ _ _ _ (contraction_over hcof hfib) q _ r

lemma snoc_face (i : Fin (n + 2)) {a : D C} {X Y : degree (D C) (n + 2)}
    (q : chain hcof hfib U a X) (f : X ⟶ Y) (t : U ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval) :
    snoc hcof hfib P n j q ((FreeGeneratorFaces.fixedFace (D C) (n + 1) i).map f) t =
      snoc hcof hfib P (n + 1) (j ≫ P ◁ SSet.stdSimplex.δ i) q f t := by
  simp only [snoc, ← OrdinaryBarFreeAmbientFamilies.family_face,
    ParameterComposition.substitute, whiskerLeft_comp, Category.assoc]

lemma snoc_degeneracy (i : Fin (n + 1)) (k : U ⟶ parameters P (n + 1))
    {a : D C} {X Y : degree (D C) (n + 1)} (q : chain hcof hfib U a X) (f : X ⟶ Y)
    (t : U ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval) :
    snoc hcof hfib P (n + 1) k q ((degeneracyFunctor (D C) n i).map f) t =
      snoc hcof hfib P n (k ≫ P ◁ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.sigma n i) q f t := by
  simp only [snoc, OrdinaryBarFreeAmbientFamilies.family_degeneracy,
    ParameterComposition.substitute, whiskerLeft_comp, Category.assoc]

omit [HomotopicalAlgebra.ModelCategory C] [HomotopicalAlgebra.ModelCategory SSet.{v}] in
lemma face_path_length (i : Fin (n + 2)) {X Y : degree (D C) (n + 2)} (q : Quiver.Path X Y) :
    ((FreeGeneratorFaces.fixedFace (D C) (n + 1) i).toPrefunctor.mapPath q).length = q.length := by
  induction q with
  | nil => rfl
  | cons q f ih => change _ + 1 = q.length + 1; rw [ih]

omit [HomotopicalAlgebra.ModelCategory C] [HomotopicalAlgebra.ModelCategory SSet.{v}] in
lemma degeneracy_path_length (i : Fin (n + 1)) {X Y : degree (D C) (n + 1)}
    (q : Quiver.Path X Y) :
    ((degeneracyFunctor (D C) n i).toPrefunctor.mapPath q).length = q.length := by
  induction q with
  | nil => rfl
  | cons q f ih => change _ + 1 = q.length + 1; rw [ih]

lemma ofPath_face (i : Fin (n + 2)) {X Y : degree (D C) (n + 2)} (q : Quiver.Path X Y)
    (t : ℕ → (U ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval)) :
    ofPath hcof hfib P n j
      ((FreeGeneratorFaces.fixedFace (D C) (n + 1) i).toPrefunctor.mapPath q) t =
    ofPath hcof hfib P (n + 1) (j ≫ P ◁ SSet.stdSimplex.δ i) q t := by
  induction q with
  | nil => rfl
  | cons q f ih =>
    simp only [Prefunctor.mapPath, ofPath]
    rw [face_path_length, ih]
    exact snoc_face hcof hfib P n j i _ f _

lemma ofPath_degeneracy (i : Fin (n + 1)) (k : U ⟶ parameters P (n + 1))
    {X Y : degree (D C) (n + 1)} (q : Quiver.Path X Y)
    (t : ℕ → (U ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval)) :
    ofPath hcof hfib P (n + 1) k ((degeneracyFunctor (D C) n i).toPrefunctor.mapPath q) t =
    ofPath hcof hfib P n (k ≫ P ◁ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.sigma n i) q t := by
  induction q with
  | nil => rfl
  | cons q f ih =>
    simp only [Prefunctor.mapPath, ofPath]
    rw [degeneracy_path_length, ih]
    exact snoc_degeneracy hcof hfib P n i k _ f _

lemma family_face (i : Fin (n + 2)) {X Y : degree (D C) (n + 2)} (q : Quiver.Path X Y)
    (t : ℕ → (U ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval)) :
    family hcof hfib P n j
      ((FreeGeneratorFaces.fixedFace (D C) (n + 1) i).toPrefunctor.mapPath q) t =
    family hcof hfib P (n + 1) (j ≫ P ◁ SSet.stdSimplex.δ i) q t :=
  congrArg (OrdinaryBarChainFamily.family hcof hfib) (ofPath_face hcof hfib P n j i q t)

lemma family_degeneracy (i : Fin (n + 1)) (k : U ⟶ parameters P (n + 1))
    {X Y : degree (D C) (n + 1)} (q : Quiver.Path X Y)
    (t : ℕ → (U ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval)) :
    family hcof hfib P (n + 1) k ((degeneracyFunctor (D C) n i).toPrefunctor.mapPath q) t =
    family hcof hfib P n (k ≫ P ◁ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.sigma n i) q t :=
  congrArg (OrdinaryBarChainFamily.family hcof hfib) (ofPath_degeneracy hcof hfib P n i k q t)

lemma evaluate_zero {X Y : degree (D C) (n + 1)} (q : Quiver.Path X Y) :
    RetractChainFamily.evaluate (ambient hcof hfib) (lifted hcof hfib)
      (section_ hcof hfib) (projection hcof hfib) (contraction hcof hfib)
        (ofPath hcof hfib P n j q (fun _ => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.zero U)) =
    ParameterComposition.substitute j (OrdinaryBarFreeAmbientFamilies.family hcof hfib P n
      ((pathComposition (degree (D C) (n + 1))).map q)) := by
  induction q with
  | nil =>
    change ParameterComposition.const U (𝟙 (ambient hcof hfib X)) =
      ParameterComposition.substitute j (OrdinaryBarFreeAmbientFamilies.family hcof hfib P n
        (FreeGeneratorCategories.identity (D C) (n + 1) X))
    rw [OrdinaryBarFreeAmbientFamilies.family_id, ParameterComposition.substitute_const]
  | cons q f ih =>
    change ParameterComposition.comp
      (RetractChainFamily.evaluate (ambient hcof hfib) (lifted hcof hfib)
        (section_ hcof hfib) (projection hcof hfib) (contraction hcof hfib)
          (ofPath hcof hfib P n j q (fun _ => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.zero U)))
      (ParameterComposition.comp
        (ParameterComposition.substitute j (OrdinaryBarFreeAmbientFamilies.family hcof hfib P n f))
        (RetractChainFamily.contraction _ _ _ _ _ _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.zero U))) =
      ParameterComposition.substitute j (OrdinaryBarFreeAmbientFamilies.family hcof hfib P n
        ((pathComposition (degree (D C) (n + 1))).map q ≫ f))
    rw [RetractChainFamily.contraction_zero, ParameterComposition.comp_id, ih,
      OrdinaryBarFreeAmbientFamilies.family_comp, ParameterComposition.substitute_comp]

lemma family_zero {X Y : degree (D C) (n + 1)} (q : Quiver.Path X Y) :
    family hcof hfib P n j q (fun _ => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.zero U) =
    OrdinaryBarFreeTransferredFamilies.ofFamily hcof hfib (ParameterComposition.substitute j
      (OrdinaryBarFreeAmbientFamilies.family hcof hfib P n
        ((pathComposition (degree (D C) (n + 1))).map q))) := by
  change ParameterComposition.comp (ParameterComposition.const U (section_ hcof hfib X))
    (ParameterComposition.comp
      (RetractChainFamily.evaluate (ambient hcof hfib) (lifted hcof hfib)
        (section_ hcof hfib) (projection hcof hfib) (contraction hcof hfib)
          (ofPath hcof hfib P n j q (fun _ => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.zero U)))
      (ParameterComposition.const U (projection hcof hfib Y))) = _
  rw [evaluate_zero]
  ext m x
  rfl

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeChainTransfer
