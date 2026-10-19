module

public import SerrePositivity.InfinityCategories.F1B.KanSectionRelativeFunctor
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
概要：固定した射影への相対関手空間を底上の対象の反変関手にする。
方針：底上の射の前合成を内部 Hom の fiber へ制限し、包含後に恒等・合成を確認する。
規約：底上の可換性を型の移送にせず、fiber への持ち上げの条件として使う。
使われ方：Kerodon Corollary 5.6.0.6、底上の同値による相対写像空間の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.KanSection

/-- 概要：底上の射は固定した射影への相対関手空間の前合成を与える。
方針：内部 Hom の前合成の自然性と底上の可換性を使い、指定した fiber へ持ち上げる。
規約：射影 p と底上の射の充填性は不要。
使われ方：Kerodon Corollary 5.6.0.6、相対写像空間の定義域の比較。 -/
def relativeFunctorOverPre {E B : SSet.{u}} (p : E ⟶ B) {a b : Over B} (f : a ⟶ b) :
    relativeFunctorSpace p b.hom ⟶ relativeFunctorSpace p a.hom :=
  vertexFiberLift _ _ (vertexFiberι _ _ ≫ (pre f.left).app E) (by
    rw [Category.assoc, ← (pre f.left).naturality p, ← Category.assoc,
      vertexFiberι_comp, SSet.const_comp]
    change SSet.const (functorVertex (f.left ≫ b.hom)) = SSet.const (functorVertex a.hom)
    rw [f.w])

/-- 概要：底上の前合成を相対関手空間の包含へ合成すると通常の前合成になる。
方針：fiber への持ち上げの射の計算則を用いる。
規約：始域の底の図式は b.hom、終域は a.hom。
使われ方：Kerodon Corollary 5.6.0.6、相対前合成の等式の検査。 -/
lemma relativeFunctorOverPre_ι {E B : SSet.{u}} (p : E ⟶ B) {a b : Over B} (f : a ⟶ b) :
    relativeFunctorOverPre p f ≫ vertexFiberι ((ihom a.left).map p) (functorVertex a.hom) =
      vertexFiberι ((ihom b.left).map p) (functorVertex b.hom) ≫ (pre f.left).app E := rfl

/-- 概要：底上の恒等射の前合成は相対関手空間の恒等射。
方針：包含へ合成し、内部 Hom の恒等射に沿う前合成を計算する。
規約：底上の対象 a は任意。
使われ方：Kerodon Corollary 5.6.0.6、相対写像空間の関手の単位則。 -/
lemma relativeFunctorOverPre_id {E B : SSet.{u}} (p : E ⟶ B) (a : Over B) :
    relativeFunctorOverPre p (𝟙 a) = 𝟙 (relativeFunctorSpace p a.hom) := by
  apply vertexFiber_hom_ext
  rw [relativeFunctorOverPre_ι]
  change _ ≫ (pre (𝟙 a.left)).app E = _
  rw [pre_id, NatTrans.id_app, Category.comp_id, Category.id_comp]

/-- 概要：底上の射の前合成は合成順序を反転する。
方針：包含後に内部 Hom の前合成の合成則を使う。
規約：f の後に g を合成する底上の射を、g の前合成の後に f の前合成へ写す。
使われ方：Kerodon Corollary 5.6.0.6、相対写像空間の関手の合成則。 -/
lemma relativeFunctorOverPre_comp {E B : SSet.{u}} (p : E ⟶ B) {a b c : Over B}
    (f : a ⟶ b) (g : b ⟶ c) :
    relativeFunctorOverPre p (f ≫ g) = relativeFunctorOverPre p g ≫ relativeFunctorOverPre p f := by
  apply vertexFiber_hom_ext
  simp only [Category.assoc, relativeFunctorOverPre_ι]
  rw [← Category.assoc, relativeFunctorOverPre_ι, Category.assoc,
    ← NatTrans.comp_app, ← pre_map]
  rfl

/-- 概要：固定射影への相対関手空間は底上の単体集合の反変関手。
方針：各対象を相対関手空間に、射を前合成に写す。
規約：left fibration の場合には各値は Kan 複体となる。
使われ方：Kerodon Corollary 5.6.0.6、分類の相対写像空間の定義域に関する関手性。 -/
def relativeFunctorOverFunctor {E B : SSet.{u}} (p : E ⟶ B) : (Over B)ᵒᵖ ⥤ SSet.{u} where
  obj a := relativeFunctorSpace p a.unop.hom
  map f := relativeFunctorOverPre p f.unop
  map_id a := relativeFunctorOverPre_id p a.unop
  map_comp f g := relativeFunctorOverPre_comp p g.unop f.unop

/-- 概要：底上の射を相対関手空間の頂点にする。
方針：functorVertex に後合成の固定条件を添える。
規約：可換性の証明の選択には依存しない。
使われ方：Kerodon Corollary 5.6.0.6、復元比較の目標となる相対関手の指定。 -/
def relativeFunctorVertex {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B)
    (f : A ⟶ E) (hf : f ≫ p = a) : (relativeFunctorSpace p a) _⦋0⦌ :=
  ⟨functorVertex f, by
    change functorVertex (f ≫ p) = PinchedHom.constant (functorVertex a) 0
    rw [hf, PinchedHom.constant_zero]⟩

/-- 概要：相対関手空間の全ての頂点は厳密な底上の射から得られる。
方針：内部 Hom の頂点を通常の射で表し、固定条件を functorVertex の単射性で戻す。
規約：底上の可換性は厳密な等式。
使われ方：Kerodon Corollary 5.6.0.6、写像空間の本質的全射性から比較射を選ぶ。 -/
lemma exists_relativeFunctorVertex {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B)
    (v : (relativeFunctorSpace p a) _⦋0⦌) :
    ∃ (f : A ⟶ E) (hf : f ≫ p = a), relativeFunctorVertex p a f hf = v := by
  obtain ⟨f, hv⟩ := (functorVertexEquiv A E).surjective v.val
  change functorVertex f = v.val at hv
  have hf : f ≫ p = a := by
    apply functorVertex_injective
    change ((ihom A).map p).app (Opposite.op ⦋0⦌) (functorVertex f) = functorVertex a
    rw [hv]
    simpa only [PinchedHom.constant_zero] using v.property
  refine ⟨f, hf, ?_⟩
  apply Subtype.ext
  exact hv

/-- 概要：底上の前合成は相対関手の頂点を射の合成の頂点へ写す。
方針：部分型の値で内部 Hom の前合成を計算する。
規約：底の可換性は底上の射から得る。
使われ方：Kerodon Corollary 5.6.0.6、相対関手の同型を比較射の制限の同型へ移す。 -/
lemma relativeFunctorOverPre_vertex {E B : SSet.{u}} (p : E ⟶ B)
    {a b : Over B} (f : a ⟶ b) (g : b.left ⟶ E) (hg : g ≫ p = b.hom) :
    (relativeFunctorOverPre p f).app (Opposite.op ⦋0⦌) (relativeFunctorVertex p b.hom g hg) =
      relativeFunctorVertex p a.hom (f.left ≫ g)
        (by rw [Category.assoc, hg, f.w]) := by
  apply Subtype.ext
  rfl

end SerrePositivity.InfinityCategories.KanSection
