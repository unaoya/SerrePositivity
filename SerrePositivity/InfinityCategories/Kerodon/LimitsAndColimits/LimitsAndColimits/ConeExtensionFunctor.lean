module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cone

/-!
概要：通常の錐の圏を WithInitial 上の関手の圏へ写す。
方針：錐の射を始点の成分と元の図式上の恒等変換で拡張する。
規約：比較射の構成と普遍性の証明を区別する。
使われ方：B5 の pointwise Kan の古典比較。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

variable {I C : Type u} [Category.{u} I] [Category.{u} C] {F : I ⥤ C}

/-- 概要：錐の射を拡張関手間の自然変換にする。
方針：始点では元の射を使い元の図式上では恒等射を使う。
規約：同じ宇宙で元の指定図式を保持する。
使われ方：B5 の局所錐と普遍性の古典比較。 -/
def coneWithInitialNatTrans {c d : Cone F} (f : c ⟶ d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneWithInitialFunctor c ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneWithInitialFunctor d where
  app x := match x with
    | WithInitial.of _ => 𝟙 _
    | WithInitial.star => f.hom
  naturality i j g := by
    cases i with
    | of i =>
      cases j with
      | of j =>
        change F.map (WithInitial.down g) ≫ 𝟙 _ = 𝟙 _ ≫ F.map (WithInitial.down g)
        simp only [Category.id_comp, Category.comp_id]
      | star => exact (WithInitial.false_of_to_star g).elim
    | star =>
      cases j with
      | of j =>
        change c.π.app j ≫ 𝟙 _ = f.hom ≫ d.π.app j
        simpa only [Category.comp_id] using (f.w j).symm
      | star =>
        change 𝟙 _ ≫ f.hom = f.hom ≫ 𝟙 _
        simp only [Category.id_comp, Category.comp_id]

/-- 概要：錐と錐の射を拡張関手の圏へ写す関手。
方針：拡張した自然変換の恒等と合成を成分で確認する。
規約：同じ宇宙で元の指定図式を保持する。
使われ方：B5 の局所錐と普遍性の古典比較。 -/
def coneExtensionFunctor : Cone F ⥤ (WithInitial I ⥤ C) where
  obj := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneWithInitialFunctor
  map := coneWithInitialNatTrans
  map_id c := by ext x; cases x <;> rfl
  map_comp f g := by
    ext x
    cases x with
    | of x => exact (Category.id_comp _).symm
    | star => rfl

/-- 概要：拡張関手の族は元の添字上で定値な図式の族になる。
方針：対象と自然変換の全ての成分で比較する。
規約：同じ宇宙で元の指定図式を保持する。
使われ方：B5 の局所錐と普遍性の古典比較。 -/
lemma coneExtensionFunctor_restrict :
    coneExtensionFunctor (F := F) ⋙
      (Functor.whiskeringLeft I (WithInitial I) C).obj WithInitial.incl =
      (Functor.const (Cone F)).obj F := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun c d f ↦ ?_)
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- 概要：拡張した錐の射の元の図式上の制限は恒等変換。
方針：元の対象上の成分の定義を読む。
規約：同じ宇宙で元の指定図式を保持する。
使われ方：B5 の局所錐と普遍性の古典比較。 -/
lemma coneWithInitialNatTrans_restrict {c d : Cone F} (f : c ⟶ d) :
    Functor.whiskerLeft WithInitial.incl (coneWithInitialNatTrans f) = 𝟙 F := rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
