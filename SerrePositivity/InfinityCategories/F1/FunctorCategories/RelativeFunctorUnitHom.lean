module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorCompositionLaws

/-!
概要：通常の底上の射と相対豊穣 Hom の単位からの射の対応。
方針：内部 Hom の頂点の同値を底の固定条件へ制限し、単位からの射の同値と合成する。
規約：通常の射の恒等・合成と豊穣単位・合成の整合性も示す。
使われ方：Kerodon Corollary 5.6.0.6、left fibrations の単体的圏の通常の射。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：底上の射と相対関手空間の頂点は全単射で対応する。
方針：通常の関手の頂点との同値を後合成の固定条件に制限する。
規約：単体集合の充填性は不要。
使われ方：Kerodon Corollary 5.6.0.6、豊穣 Hom の通常の射の回収。 -/
noncomputable def relativeFunctorVertexEquiv {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) :
    {f : A ⟶ E // f ≫ p = a} ≃ (relativeFunctorSpace p a) _⦋0⦌ :=
  Equiv.subtypeEquiv (functorVertexEquiv A E) (by
    intro f
    change f ≫ p = a ↔ functorVertex (f ≫ p) = PinchedHom.constant (functorVertex a) 0
    rw [PinchedHom.constant_zero]
    exact ⟨congrArg functorVertex, fun h ↦ functorVertex_injective h⟩)

/-- 概要：Over 圏の射を底を保つ単体集合の射の部分型と同定する。
方針：底上の射の左成分と可換性を取り出し、逆に homMk で構成する。
規約：同型ではなく通常の型の全単射。
使われ方：Kerodon Corollary 5.6.0.6、豊穣単位から通常の射への対応。 -/
def overHomEquivSubtype {B : SSet.{u}} (a b : Over B) :
    (a ⟶ b) ≃ {f : a.left ⟶ b.left // f ≫ b.hom = a.hom} where
  toFun f := ⟨f.left, f.w⟩
  invFun f := Over.homMk f.val f.property
  left_inv f := by
    apply Over.OverMorphism.ext
    rfl
  right_inv f := rfl

/-- 概要：底上の通常の射と相対豊穣 Hom の単位からの射は全単射。
方針：底上の射の部分型表示、相対関手の頂点、単体集合の単位からの射を順に同定する。
規約：各対象の射影の充填性は不要。
使われ方：Kerodon Corollary 5.6.0.6、相対関手空間を Hom とする単体的圏。 -/
noncomputable def relativeFunctorHomEquiv {B : SSet.{u}} (a b : Over B) :
    (a ⟶ b) ≃ (𝟙_ SSet.{u} ⟶ relativeFunctorSpace b.hom a.hom) :=
  (overHomEquivSubtype a b).trans
    ((relativeFunctorVertexEquiv b.hom a.hom).trans (SSet.unitHomEquiv _).symm)

/-- 概要：通常の底上の射に対応する豊穣射を含めると閉構造の curry' になる。
方針：単位からの射の同値で比較し、零単体の部分型の値を計算する。
規約：比較する通常の射は Over 圏の左成分。
使われ方：Kerodon Corollary 5.6.0.6、通常の射と豊穣合成の整合性。 -/
lemma relativeFunctorHomEquiv_ι {B : SSet.{u}} {a b : Over B} (f : a ⟶ b) :
    relativeFunctorHomEquiv a b f ≫
      vertexFiberι ((ihom a.left).map b.hom) (functorVertex a.hom) = curry' f.left := by
  apply (SSet.unitHomEquiv _).injective
  change (vertexFiberι ((ihom a.left).map b.hom) (functorVertex a.hom)).app
    (Opposite.op ⦋0⦌)
    ((SSet.unitHomEquiv _)
      ((SSet.unitHomEquiv _).symm (relativeFunctorVertex b.hom a.hom f.left f.w))) =
    functorVertex f.left
  rw [Equiv.apply_symm_apply]
  rfl

/-- 概要：恒等の底上の射に対応する豊穣射は相対豊穣単位。
方針：内部 Hom への単射な包含で比較し、閉構造の恒等射の式を使う。
規約：通常の恒等射は Over 圏の恒等射。
使われ方：Kerodon Corollary 5.6.0.6、単体的圏の単位の整合性。 -/
lemma relativeFunctorHomEquiv_id {B : SSet.{u}} (a : Over B) :
    relativeFunctorHomEquiv a a (𝟙 a) = relativeFunctorIdentity a := by
  apply (cancel_mono (vertexFiberι ((ihom a.left).map a.hom) (functorVertex a.hom))).1
  rw [relativeFunctorHomEquiv_ι, relativeFunctorIdentity_ι]
  exact curry'_id a.left

/-- 概要：通常の底上の射の合成は相対豊穣合成に対応する。
方針：内部 Hom の合成に移し、二つの単位からの射を tensor の合成則でまとめる。
規約：合成の順は f、次に g。
使われ方：Kerodon Corollary 5.6.0.6、単体的圏の合成の整合性。 -/
lemma relativeFunctorHomEquiv_comp {B : SSet.{u}} {a b c : Over B}
    (f : a ⟶ b) (g : b ⟶ c) :
    relativeFunctorHomEquiv a c (f ≫ g) =
      (λ_ (𝟙_ SSet.{u})).inv ≫
        (relativeFunctorHomEquiv a b f ⊗ₘ relativeFunctorHomEquiv b c g) ≫
          relativeFunctorComposition a b c := by
  apply (cancel_mono (vertexFiberι ((ihom a.left).map c.hom) (functorVertex a.hom))).1
  rw [relativeFunctorHomEquiv_ι, Category.assoc, Category.assoc, relativeFunctorComposition_ι]
  have ht := tensorHom_comp_tensorHom (relativeFunctorHomEquiv a b f)
    (relativeFunctorHomEquiv b c g)
    (vertexFiberι ((ihom a.left).map b.hom) (functorVertex a.hom))
    (vertexFiberι ((ihom b.left).map c.hom) (functorVertex b.hom))
  rw [relativeFunctorHomEquiv_ι, relativeFunctorHomEquiv_ι] at ht
  have h := congrArg (fun k ↦ (λ_ (𝟙_ SSet.{u})).inv ≫ k ≫
    MonoidalClosed.comp a.left b.left c.left) ht
  exact (curry'_comp f.left g.left).trans (by
    simpa only [Category.assoc] using h.symm)

end SerrePositivity.InfinityCategories
