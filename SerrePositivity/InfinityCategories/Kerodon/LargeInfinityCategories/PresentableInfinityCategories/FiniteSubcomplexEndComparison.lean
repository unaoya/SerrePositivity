module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.TwistedHomEndRestriction
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FiniteSubcomplexes

/-!
概要：有限部分複体に制限した関手の twisted Hom と end 切断を一つの比較図式に束ねる。
方針：包含への制限の恒等・合成則を関手の公理とし、実切断比較の可換性を使う。
規約：部分複体の添字と元の包含をそのまま保持する。
使われ方：有限部分形状から一般の end 比較へ降下するための全自然な比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：有限部分複体への制限の間の包含。
方針：反対順序圏の射を元の部分複体の包含へ戻す。
規約：有限性の証明以外のデータを変えない。使われ方：二つの制限図式の共通の射。 -/
def finiteSubcomplexRestrictionMap {A : SSet.{u}}
    {K L : (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteSubcomplex A)ᵒᵖ} (f : K ⟶ L) :
    L.unop.val.toSSet ⟶ K.unop.val.toSSet :=
  Subcomplex.homOfLE (leOfHom f.unop)

/-- 概要：有限部分複体上の元の関手の twisted Hom の制限図式。
方針：元の二関手を包含で制限し、twisted Hom の前合成を射に使う。
規約：通常の図式で全ての包含を同時に扱う。使われ方：写像空間の有限部分への降下。 -/
def finiteSubcomplexTwistedHomDiagram {A C : SSet.{u}} (F G : A ⟶ C) :
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteSubcomplex A)ᵒᵖ ⥤ SSet.{u} where
  obj K := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowHomSpace
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (K.unop.val.ι ≫ F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (K.unop.val.ι ≫ G))
  map {K _L} f := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.twistedFunctorHomRestriction (finiteSubcomplexRestrictionMap f)
    (K.unop.val.ι ≫ F) (K.unop.val.ι ≫ G)
  map_id _ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.twistedFunctorHomRestriction_id _ _
  map_comp {K _L _M} f g := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.twistedFunctorHomRestriction_comp
    (finiteSubcomplexRestrictionMap f) (finiteSubcomplexRestrictionMap g)
    (K.unop.val.ι ≫ F) (K.unop.val.ι ≫ G)).symm

/-- 概要：有限部分複体上の end 係数の切断空間の制限図式。
方針：同じ二関手の制限を end の実 pullback と切断に入れる。
規約：頂点ごとの選択でなく一つの通常の関手にする。
使われ方：end の切断空間の有限部分への降下。 -/
def finiteSubcomplexEndSectionsDiagram {A C : SSet.{u}} (F G : A ⟶ C) :
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteSubcomplex A)ᵒᵖ ⥤ SSet.{u} where
  obj K := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorEndProjection (K.unop.val.ι ≫ F) (K.unop.val.ι ≫ G))
  map {K _L} f := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorEndSectionsRestriction (finiteSubcomplexRestrictionMap f)
    (K.unop.val.ι ≫ F) (K.unop.val.ι ≫ G)
  map_id _ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorEndSectionsRestriction_id _ _
  map_comp {K _L _M} f g := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorEndSectionsRestriction_comp
    (finiteSubcomplexRestrictionMap f) (finiteSubcomplexRestrictionMap g)
    (K.unop.val.ι ≫ F) (K.unop.val.ι ≫ G)).symm

/-- 概要：有限部分複体上の twisted Hom と end 切断の全自然な比較。
方針：構成した実比較射を成分とし、始域の制限正方形を自然性に使う。
規約：各成分の同値性はこの宣言では結論しない。
使われ方：有限部分から一般の写像空間の end 表示へ進む入力。 -/
def finiteSubcomplexEndComparison {A C : SSet.{u}} (F G : A ⟶ C) :
    finiteSubcomplexTwistedHomDiagram F G ⟶ finiteSubcomplexEndSectionsDiagram F G where
  app K := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.twistedFunctorHomToEndSections (K.unop.val.ι ≫ F) (K.unop.val.ι ≫ G)
  naturality {K _L} f := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.twistedFunctorHomToEndSections_precomp
    (finiteSubcomplexRestrictionMap f) (K.unop.val.ι ≫ F) (K.unop.val.ι ≫ G)

/-- 概要：元の全 twisted Hom から有限部分への制限を脚とする錐。
方針：全ての有限部分複体の包含へ元の二関手を制限する。
規約：頂点は元の全 twisted Hom。使われ方：有限部分からの降下の普遍性の入力。 -/
def finiteSubcomplexTwistedHomCone {A C : SSet.{u}} (F G : A ⟶ C) :
    Cone (finiteSubcomplexTwistedHomDiagram F G) where
  pt := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowHomSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)
  π := {
    app K := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.twistedFunctorHomRestriction K.unop.val.ι F G
    naturality {K _L} f := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.twistedFunctorHomRestriction_comp K.unop.val.ι
      (finiteSubcomplexRestrictionMap f) F G).symm }

/-- 概要：元の全 end 切断から有限部分への制限を脚とする錐。
方針：全ての包含への切断の制限をまとめる。
規約：各有限部分の切断を個別に選ばない。使われ方：end の切断空間の降下。 -/
def finiteSubcomplexEndSectionsCone {A C : SSet.{u}} (F G : A ⟶ C) :
    Cone (finiteSubcomplexEndSectionsDiagram F G) where
  pt := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorEndProjection F G)
  π := {
    app K := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorEndSectionsRestriction K.unop.val.ι F G
    naturality {K _L} f := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorEndSectionsRestriction_comp K.unop.val.ι
      (finiteSubcomplexRestrictionMap f) F G).symm }

/-- 概要：実切断比較は有限部分への制限錐の射を与える。
方針：各包含に対する実比較の制限正方形を錐の可換性に使う。
規約：頂点の射は構成済みの元の実比較。
使われ方：有限部分の極限表示から全体の比較を検出する。 -/
def finiteSubcomplexEndComparisonConeMorphism {A C : SSet.{u}} (F G : A ⟶ C) :
    (Cone.postcompose (finiteSubcomplexEndComparison F G)).obj
      (finiteSubcomplexTwistedHomCone F G) ⟶ finiteSubcomplexEndSectionsCone F G where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.twistedFunctorHomToEndSections F G
  w K := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.twistedFunctorHomToEndSections_precomp K.unop.val.ι F G).symm

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
