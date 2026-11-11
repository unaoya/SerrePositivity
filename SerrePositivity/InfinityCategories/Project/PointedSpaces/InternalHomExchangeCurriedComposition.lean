module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeComposition

/-!
概要：内部 Hom の合成と cotensor 交換の整合式を、同じ一度 curry した族として表示する。
方針：元の全パラメータ合成式を curry し、strength の随伴式で厳密に照合する。
規約：閉対称モノイダル圏の射の等式。使われ方：前合成区間と cotensor の交換。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.InternalHomExchange
end SerrePositivity.KST.Spectra.InternalHomExchange
namespace SerrePositivity.InfinityCategories.Project.PointedSpaces
open _root_.SerrePositivity.KST.Spectra.InternalHomExchange
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C]

/-- 同じ豊穣合成の curry は、源交換とパラメータ内部 Hom に厳密に両立する。 -/
lemma curriedComposition (W D P Z : C) :
    curry (MonoidalClosed.comp W D ((ihom P).obj Z)) ≫
        (ihom ((ihom W).obj D)).map (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso W P Z).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso D P Z).hom ≫ (ihom P).map (curry (MonoidalClosed.comp W D Z)) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso P ((ihom W).obj D) ((ihom W).obj Z)).hom := by
  have h := congrArg (fun f => curry f) (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.composition W D P Z)
  simp only [id_tensorHom] at h
  rw [curry_natural_right, curry_natural_left, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.curry_strength] at h
  simpa only [Category.assoc] using h

end SerrePositivity.InfinityCategories.Project.PointedSpaces

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.InternalHomExchange.curriedComposition := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.curriedComposition
