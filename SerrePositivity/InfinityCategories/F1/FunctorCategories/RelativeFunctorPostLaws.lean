module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorPostHomOrdinary

/-!
概要：底を保つ後合成の恒等・合成則と相対関手頂点での計算。
方針：F2 の既存の後合成を用い、fiber の包含後に内部 Hom の関手則を適用する。
規約：F2 のファイルは読むだけ。底と定義域は任意。
使われ方：Kerodon Corollary 5.6.0.6、相対写像空間の標的の同値による比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：底上の恒等射による相対後合成は恒等射。
方針：fiber の包含後に内部 Hom の恒等則を使う。
規約：充填性は不要。
使われ方：Kerodon Corollary 5.6.0.6、相対後合成の単位則。 -/
lemma relativeFunctorPost_id {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) :
    HomotopyLimits.relativeFunctorPost p p (𝟙 E) (Category.id_comp p) a =
      𝟙 (relativeFunctorSpace p a) := by
  apply vertexFiber_hom_ext ((ihom A).map p) (functorVertex a)
  rw [HomotopyLimits.relativeFunctorPost_ι, (ihom A).map_id, Category.comp_id, Category.id_comp]

/-- 概要：底上の射の合成による相対後合成は二つの相対後合成の合成に等しい。
方針：fiber の包含後に内部 Hom の合成則を使う。
規約：底上の可換性の証明の選択には依存しない。
使われ方：Kerodon Corollary 5.6.0.6、相対後合成の逆射の構成。 -/
lemma relativeFunctorPost_comp {A E F G B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (r : G ⟶ B)
    (f : E ⟶ F) (hf : f ≫ q = p) (g : F ⟶ G) (hg : g ≫ r = q) (a : A ⟶ B) :
    HomotopyLimits.relativeFunctorPost p q f hf a ≫ HomotopyLimits.relativeFunctorPost q r g hg a =
      HomotopyLimits.relativeFunctorPost p r (f ≫ g)
        (by rw [Category.assoc, hg, hf]) a := by
  apply vertexFiber_hom_ext ((ihom A).map r) (functorVertex a)
  rw [Category.assoc, HomotopyLimits.relativeFunctorPost_ι, ← Category.assoc,
    HomotopyLimits.relativeFunctorPost_ι, HomotopyLimits.relativeFunctorPost_ι,
    (ihom A).map_comp, Category.assoc]

/-- 概要：相対後合成は底上の射の相対頂点を通常の射の合成の相対頂点へ写す。
方針：相対頂点の内部 Hom 成分で計算する。
規約：元の底の図式 a は固定する。
使われ方：Kerodon Corollary 5.6.0.6、相対的な単位・余単位の後合成。 -/
lemma relativeFunctorPost_vertex {A E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (f : E ⟶ F) (hf : f ≫ q = p)
    (a : A ⟶ B) (g : A ⟶ E) (hg : g ≫ p = a) :
    (HomotopyLimits.relativeFunctorPost p q f hf a).app _ (relativeFunctorVertex p a g hg) =
      relativeFunctorVertex q a (g ≫ f) (by rw [Category.assoc, hf, hg]) := by
  apply Subtype.ext
  rfl

/-- 概要：豊穣後合成は通常の射の相対頂点を通常の相対後合成の関手頂点へ写す。
方針：通常の後合成との単位からの射での一致を、零単体へ評価する。
規約：底上の対象 a、b、c の充填性は不要。
使われ方：Kerodon Corollary 5.6.0.6、相対頂点間の同型から後合成の関手同型を得る。 -/
lemma relativeFunctorPostHom_vertex {B : SSet.{u}} (a b c : Over B) (f : b ⟶ c) :
    (relativeFunctorPostHom a b c).app _ (relativeFunctorVertex c.hom b.hom f.left f.w) =
      functorVertex (HomotopyLimits.relativeFunctorPost b.hom c.hom f.left f.w a.hom) := by
  have h := congrArg (SSet.unitHomEquiv _) (relativeFunctorPostHom_ordinary a b c f)
  change (relativeFunctorPostHom a b c).app (Opposite.op ⦋0⦌)
    ((SSet.unitHomEquiv _) ((SSet.unitHomEquiv _).symm
      (relativeFunctorVertex c.hom b.hom f.left f.w))) = _ at h
  rw [Equiv.apply_symm_apply] at h
  exact h

end SerrePositivity.InfinityCategories
