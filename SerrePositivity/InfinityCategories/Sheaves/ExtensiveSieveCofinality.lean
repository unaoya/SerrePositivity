module

public import SerrePositivity.InfinityCategories.Sheaves.ExtensiveSieveIndex
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.NerveAdjunction
public import Mathlib.CategoryTheory.Adjunction.Comma

/-!
概要：非空の有限余積の脚と初対象からなる添字は、元の生成篩の反対で left cofinal。
方針：各 comma の終対象を、始域が初対象の場合とそうでない場合に分けて示す。
規約：HTT 4.1.3.1、Kerodon Theorem 7.2.3.1（Tag 02NY）の指定随伴による特殊化。
使われ方：S1 の extensive 層条件と元の有限積錐の比較。空族は別に扱う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {ι : Type u} {B : ι → C}

/-- 初対象を始域とする篩の対象は、添字の star から同じ三角形を持つ。 -/
def cofanInitialCommaObj [HasInitial C] [Nonempty ι] (c : Cofan B)
    (s : (sieveCategory (cofanGeneratedSieve c))ᵒᵖ) (hV : IsInitial s.unop.obj.left) :
    CostructuredArrow (cofanSieveIndex c) s :=
  CostructuredArrow.mk (Y := WithTerminal.star)
    ((ObjectProperty.homMk (Over.homMk (hV.to (⊥_ C)) (by apply hV.hom_ext))).op)

/-- 始域が初対象の場合は、元の star の三角形が comma の終対象。 -/
def cofanInitialComma_isTerminal [HasInitial C] [Nonempty ι] (c : Cofan B)
    (s : (sieveCategory (cofanGeneratedSieve c))ᵒᵖ) (hV : IsInitial s.unop.obj.left) :
    IsTerminal (cofanInitialCommaObj c s hV) := by
  refine IsTerminal.ofUniqueHom (fun a => CostructuredArrow.homMk
    (WithTerminal.starTerminal.from a.left) ?_) ?_
  · apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact hV.hom_ext _ _
  · intro a f
    apply CostructuredArrow.hom_ext
    exact WithTerminal.starTerminal.hom_ext _ _

/-- 一本の脚への分解は、元の同じ射を持つ comma の対象になる。 -/
def cofanLegCommaObj [HasInitial C] [Nonempty ι] (c : Cofan B)
    (s : (sieveCategory (cofanGeneratedSieve c))ᵒᵖ) (i : ι)
    (f : s.unop.obj.left ⟶ B i) (hf : f ≫ c.inj i = s.unop.obj.hom) :
    CostructuredArrow (cofanSieveIndex c) s :=
  CostructuredArrow.mk (Y := WithTerminal.of (Discrete.mk i))
    ((ObjectProperty.homMk (Over.homMk f hf)).op)

/-- 初対象でない場合は、一意な脚への元の分解へすべての三角形を戻す。 -/
def cofanLegCommaTo [FinitaryExtensive C] [Finite ι] [Nonempty ι]
    (c : Cofan B) (hc : IsColimit c)
    (s : (sieveCategory (cofanGeneratedSieve c))ᵒᵖ)
    (hV : ¬ Nonempty (IsInitial s.unop.obj.left)) (i : ι)
    (f : s.unop.obj.left ⟶ B i) (hf : f ≫ c.inj i = s.unop.obj.hom)
    (a : CostructuredArrow (cofanSieveIndex c) s) : a ⟶ cofanLegCommaObj c s i f hf := by
  rcases a with ⟨a, b, α⟩
  cases a with
  | star =>
      exact False.elim (hV ⟨IsInitial.ofStrict α.unop.hom.left initialIsInitial⟩)
  | of j =>
      have hj : j.as = i := cofanFactorization_label_unique c hc hV
        α.unop.hom.left f ((Over.w α.unop.hom).trans hf.symm)
      cases j with
      | mk j =>
          change j = i at hj
          subst j
          refine CostructuredArrow.homMk (𝟙 _) ?_
          rw [CategoryTheory.Functor.map_id, Category.id_comp]
          apply Quiver.Hom.unop_inj
          apply ObjectProperty.hom_ext
          apply Over.OverMorphism.ext
          exact cofanFactorization_arrow_unique c hc i f α.unop.hom.left
            (hf.trans (Over.w α.unop.hom).symm)

/-- 初対象でない始域では、その一意な脚の三角形が comma の終対象。 -/
def cofanLegComma_isTerminal [FinitaryExtensive C] [Finite ι] [Nonempty ι]
    (c : Cofan B) (hc : IsColimit c)
    (s : (sieveCategory (cofanGeneratedSieve c))ᵒᵖ)
    (hV : ¬ Nonempty (IsInitial s.unop.obj.left)) (i : ι)
    (f : s.unop.obj.left ⟶ B i) (hf : f ≫ c.inj i = s.unop.obj.hom) :
    IsTerminal (cofanLegCommaObj c s i f hf) :=
  IsTerminal.ofUniqueHom (cofanLegCommaTo c hc s hV i f hf) (fun a g => by
    apply CostructuredArrow.hom_ext
    exact Subsingleton.elim _ _)

/-- 元の全篩の対象について、どちらの枝でも comma の終対象が存在する。 -/
lemma cofanSieveIndex_hasTerminalComma [FinitaryExtensive C] [Finite ι] [Nonempty ι]
    (c : Cofan B) (hc : IsColimit c) (s : (sieveCategory (cofanGeneratedSieve c))ᵒᵖ) :
    HasTerminal (CostructuredArrow (cofanSieveIndex c) s) := by
  classical
  by_cases hV : Nonempty (IsInitial s.unop.obj.left)
  · exact (cofanInitialComma_isTerminal c s hV.some).hasTerminal
  · obtain ⟨i, f, hf⟩ := cofanSieveFactorization c s.unop
    exact (cofanLegComma_isTerminal c hc s hV i f hf.symm).hasTerminal

/-- 指定した添字関手は元の生成篩の反対で left cofinal。
新しい Quillen A の構成を使わず、同じ comma の終対象からの随伴を渡す。 -/
lemma cofanSieveIndex_isLeftCofinal [FinitaryExtensive C] [Finite ι] [Nonempty ι]
    (c : Cofan B) (hc : IsColimit c) : IsLeftCofinal (nerveMap (cofanSieveIndex c)) := by
  letI (s : (sieveCategory (cofanGeneratedSieve c))ᵒᵖ) :
      HasTerminal (CostructuredArrow (cofanSieveIndex c) s) :=
    cofanSieveIndex_hasTerminalComma c hc s
  exact nerveMap_isLeftCofinal_of_adjunction
    (CategoryTheory.adjunctionOfCostructuredArrowTerminals (cofanSieveIndex c))

end SerrePositivity.InfinityCategories.Sheaves
