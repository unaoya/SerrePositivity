module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeChainTransfer

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeTransferredFamilies
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarWordChainFamily

/-!
# 中断した任意モデル源への一般化：OrdinaryBarFreeWordChainTransfer

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：All free-resolution degrees with actual word-parameter chain transfer。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0195][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0195
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# All free-resolution degrees with actual word-parameter chain transfer

Arbitrary source chains retain all face, degeneracy, and substitution
identities. Internal identities are removed by concatenating word parameters.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeWordChainTransfer
open FreeGeneratorCategories OrdinaryBarFreeResolutionSeed OrdinaryBarChoiceBoundaryGluing
open OrdinaryBarRetractSystem
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v}) (n : ℕ)

abbrev chain (U : SSet.{max u v}) (X Y : D C) := OrdinaryBarWordChainFamily.chain hcof hfib U X Y

variable {U V : SSet.{max u v}} (j : U ⟶ parameters P n)

def snoc {a : D C} {X Y : degree (D C) (n + 1)} (q : chain hcof hfib U a X)
    (f : X ⟶ Y) (t : U ⟶ WordSegment.obj) : chain hcof hfib U a Y :=
  q.familySnoc (ParameterComposition.substitute j
    (OrdinaryBarFreeAmbientFamilies.family hcof hfib P n f)) t

lemma snoc_substitute (k : V ⟶ U) {a : D C} {X Y : degree (D C) (n + 1)}
    (q : chain hcof hfib U a X) (f : X ⟶ Y) (t : U ⟶ WordSegment.obj) :
    (snoc hcof hfib P n j q f t).substitute k =
      snoc hcof hfib P n (k ≫ j) (q.substitute k) f (k ≫ t) := by
  simp only [snoc, WordRetractChainFamily.Chain.substitute, ParameterComposition.substitute,
    whiskerLeft_comp, Category.assoc]

def ofPath {X : degree (D C) (n + 1)} :
    {Y : degree (D C) (n + 1)} → Quiver.Path X Y →
      (ℕ → (U ⟶ WordSegment.obj)) → chain hcof hfib U X Y
  | _, .nil, _ => .nil
  | _, .cons q f, t => snoc hcof hfib P n j (ofPath q t) f (t q.length)

lemma ofPath_length {X Y : degree (D C) (n + 1)} (q : Quiver.Path X Y)
    (t : ℕ → (U ⟶ WordSegment.obj)) :
    (ofPath hcof hfib P n j q t).length = q.length := by
  induction q with
  | nil => rfl
  | cons q f ih => change (ofPath hcof hfib P n j q t).length + 1 = q.length + 1; rw [ih]

lemma ofPath_substitute (k : V ⟶ U) {X Y : degree (D C) (n + 1)} (q : Quiver.Path X Y)
    (t : ℕ → (U ⟶ WordSegment.obj)) :
    (ofPath hcof hfib P n j q t).substitute k =
      ofPath hcof hfib P n (k ≫ j) q (fun r => k ≫ t r) := by
  induction q with
  | nil => rfl
  | cons q f ih => simp only [ofPath, snoc_substitute, ih]

def family {X Y : degree (D C) (n + 1)} (q : Quiver.Path X Y)
    (t : ℕ → (U ⟶ WordSegment.obj)) : lifted hcof hfib X ⊗ U ⟶ lifted hcof hfib Y :=
  OrdinaryBarWordChainFamily.family hcof hfib (ofPath hcof hfib P n j q t)

lemma family_substitute (k : V ⟶ U) {X Y : degree (D C) (n + 1)} (q : Quiver.Path X Y)
    (t : ℕ → (U ⟶ WordSegment.obj)) :
    family hcof hfib P n (k ≫ j) q (fun r => k ≫ t r) =
      ParameterComposition.substitute k (family hcof hfib P n j q t) := by
  rw [family, ← ofPath_substitute, OrdinaryBarWordChainFamily.family_substitute]
  rfl

lemma family_nil (X : degree (D C) (n + 1)) (t : ℕ → (U ⟶ WordSegment.obj)) :
    family hcof hfib P n j (Quiver.Path.nil : Quiver.Path X X) t = fst (lifted hcof hfib X) U := by
  ext m x
  exact types_congr_hom (congr_app (section_fac hcof hfib X) m) x.1

lemma family_single {X Y : degree (D C) (n + 1)} (f : X ⟶ Y)
    (t : ℕ → (U ⟶ WordSegment.obj)) :
    family hcof hfib P n j f.toPath t =
      OrdinaryBarFreeTransferredFamilies.ofFamily hcof hfib (ParameterComposition.substitute j
        (OrdinaryBarFreeAmbientFamilies.family hcof hfib P n f)) := by
  refine (WordRetractChainFamily.transfer_last_family_parameter
    (ambient hcof hfib) (lifted hcof hfib)
    (section_ hcof hfib) (projection hcof hfib) (section_fac hcof hfib) (contraction hcof hfib)
    (contraction_over hcof hfib) (contraction_on_section hcof hfib)
    (.nil : chain hcof hfib U X X)
    (ParameterComposition.substitute j (OrdinaryBarFreeAmbientFamilies.family hcof hfib P n f))
    (t 0)).trans ?_
  ext m x
  rfl

lemma unit_face {a d : D C} {X Y Z : degree (D C) (n + 1)}
    (q : chain hcof hfib U a X) (f : X ⟶ Y) (g : Y ⟶ Z)
    (t : U ⟶ WordSegment.obj) (r : chain hcof hfib U Z d) :
    OrdinaryBarWordChainFamily.family hcof hfib
      ((snoc hcof hfib P n j (snoc hcof hfib P n j q f (WordSegment.unitAt U)) g t).append r) =
    OrdinaryBarWordChainFamily.family hcof hfib ((snoc hcof hfib P n j q (f ≫ g) t).append r) := by
  have hh := WordRetractChainFamily.unit_family_face (ambient hcof hfib) (lifted hcof hfib)
    (section_ hcof hfib) (projection hcof hfib) (section_fac hcof hfib) (contraction hcof hfib)
    (contraction_over hcof hfib) (contraction_on_section hcof hfib) q
    (ParameterComposition.substitute j (OrdinaryBarFreeAmbientFamilies.family hcof hfib P n f))
    (ParameterComposition.substitute j (OrdinaryBarFreeAmbientFamilies.family hcof hfib P n g)) t r
  simpa only [snoc, OrdinaryBarWordChainFamily.family, OrdinaryBarFreeAmbientFamilies.family_comp,
    ParameterComposition.substitute_comp] using hh

lemma zero_face {a d : D C} {X Y : degree (D C) (n + 1)}
    (q : chain hcof hfib U a X) (f : X ⟶ Y) (r : chain hcof hfib U Y d) :
    OrdinaryBarWordChainFamily.family hcof hfib
      ((snoc hcof hfib P n j q f (WordSegment.zeroAt U)).append r) =
    ParameterComposition.comp
      (OrdinaryBarWordChainFamily.family hcof hfib
        (snoc hcof hfib P n j q f (WordSegment.unitAt U)))
      (OrdinaryBarWordChainFamily.family hcof hfib r) :=
  WordRetractChainFamily.zero_family_face _ _ _ _ _ _ _ _ q _ r

lemma snoc_face (i : Fin (n + 2)) {a : D C} {X Y : degree (D C) (n + 2)}
    (q : chain hcof hfib U a X) (f : X ⟶ Y) (t : U ⟶ WordSegment.obj) :
    snoc hcof hfib P n j q ((FreeGeneratorFaces.fixedFace (D C) (n + 1) i).map f) t =
      snoc hcof hfib P (n + 1) (j ≫ P ◁ SSet.stdSimplex.δ i) q f t := by
  simp only [snoc, ← OrdinaryBarFreeAmbientFamilies.family_face,
    ParameterComposition.substitute, whiskerLeft_comp, Category.assoc]

lemma snoc_degeneracy (i : Fin (n + 1)) (k : U ⟶ parameters P (n + 1))
    {a : D C} {X Y : degree (D C) (n + 1)} (q : chain hcof hfib U a X) (f : X ⟶ Y)
    (t : U ⟶ WordSegment.obj) :
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
    (t : ℕ → (U ⟶ WordSegment.obj)) :
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
    (t : ℕ → (U ⟶ WordSegment.obj)) :
    ofPath hcof hfib P (n + 1) k ((degeneracyFunctor (D C) n i).toPrefunctor.mapPath q) t =
    ofPath hcof hfib P n (k ≫ P ◁ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.sigma n i) q t := by
  induction q with
  | nil => rfl
  | cons q f ih =>
    simp only [Prefunctor.mapPath, ofPath]
    rw [degeneracy_path_length, ih]
    exact snoc_degeneracy hcof hfib P n i k _ f _

lemma family_face (i : Fin (n + 2)) {X Y : degree (D C) (n + 2)} (q : Quiver.Path X Y)
    (t : ℕ → (U ⟶ WordSegment.obj)) :
    family hcof hfib P n j
      ((FreeGeneratorFaces.fixedFace (D C) (n + 1) i).toPrefunctor.mapPath q) t =
    family hcof hfib P (n + 1) (j ≫ P ◁ SSet.stdSimplex.δ i) q t :=
  congrArg (OrdinaryBarWordChainFamily.family hcof hfib) (ofPath_face hcof hfib P n j i q t)

lemma family_degeneracy (i : Fin (n + 1)) (k : U ⟶ parameters P (n + 1))
    {X Y : degree (D C) (n + 1)} (q : Quiver.Path X Y)
    (t : ℕ → (U ⟶ WordSegment.obj)) :
    family hcof hfib P (n + 1) k ((degeneracyFunctor (D C) n i).toPrefunctor.mapPath q) t =
    family hcof hfib P n (k ≫ P ◁ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.sigma n i) q t :=
  congrArg (OrdinaryBarWordChainFamily.family hcof hfib) (ofPath_degeneracy hcof hfib P n i k q t)

lemma interior_identity {a d : D C} {X Y : degree (D C) (n + 1)}
    (q : chain hcof hfib U a X) (f : X ⟶ Y) (t w : U ⟶ WordSegment.obj)
    (r : chain hcof hfib U Y d) :
    OrdinaryBarWordChainFamily.family hcof hfib
      ((snoc hcof hfib P n j (snoc hcof hfib P n j q f t)
        (FreeGeneratorCategories.identity (D C) (n + 1) Y) w).append r) =
      OrdinaryBarWordChainFamily.family hcof hfib
        ((snoc hcof hfib P n j q f (lift t w ≫ WordSegment.mul)).append r) := by
  unfold snoc
  rw [OrdinaryBarFreeAmbientFamilies.family_id, ParameterComposition.substitute_const]
  exact OrdinaryBarWordChainFamily.interior_identity hcof hfib q _ t w r

lemma small_interior_identity {T : SSet.{v}}
    (k : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ parameters P n) {a d : D C}
    {X Y : degree (D C) (n + 1)}
    (q : chain hcof hfib (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T) a X) (f : X ⟶ Y)
    (t w : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ WordSegment.obj)
    (r : chain hcof hfib (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T) Y d) :
    OrdinaryBarWordChainFamily.smallFamily hcof hfib
      ((snoc hcof hfib P n k (snoc hcof hfib P n k q f t)
        (FreeGeneratorCategories.identity (D C) (n + 1) Y) w).append r) =
      OrdinaryBarWordChainFamily.smallFamily hcof hfib
        ((snoc hcof hfib P n k q f (lift t w ≫ WordSegment.mul)).append r) :=
  congrArg _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.lowerTensor (interior_identity hcof hfib P n k q f t w r)

lemma ofPath_ofInterval {X Y : degree (D C) (n + 1)} (q : Quiver.Path X Y)
    (t : ℕ → (U ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval)) :
    WordRetractChainFamily.Chain.ofInterval
      (OrdinaryBarFreeChainTransfer.ofPath hcof hfib P n j q t) =
      ofPath hcof hfib P n j q (fun k => t k ≫ WordSegment.letter) := by
  induction q with
  | nil => rfl
  | cons q f ih =>
    change (WordRetractChainFamily.Chain.ofInterval
      (OrdinaryBarFreeChainTransfer.ofPath hcof hfib P n j q t)).familySnoc _ _ = _
    rw [ih]
    rfl

lemma family_ofInterval {X Y : degree (D C) (n + 1)} (q : Quiver.Path X Y)
    (t : ℕ → (U ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval)) :
    family hcof hfib P n j q (fun k => t k ≫ WordSegment.letter) =
      OrdinaryBarFreeChainTransfer.family hcof hfib P n j q t := by
  rw [family, ← ofPath_ofInterval, OrdinaryBarWordChainFamily.family_ofInterval]
  rfl

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeWordChainTransfer
