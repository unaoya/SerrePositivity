module
public import SerrePositivity.InfinityCategories.Derived.SemifreeCofiberZeroTriangle
public import SerrePositivity.InfinityCategories.Derived.CofiberSuspensionSquareHom
public import SerrePositivity.InfinityCategories.Derived.FullFunctorHomotopyLift
public import SerrePositivity.InfinityCategories.Derived.SuspensionSquareHomotopy

/-! # Semifree 内の cofiber から suspension への四角形比較射

概要：全複体で構成した二段比較を Semifree 内の関手圏の h の射へ持ち上げる。
方針：両端を包含像に正規化し、充満 dg 部分圏への図式射の持ち上げを使う。
規約：包含後の射を Arrow の等式で保持する。使われ方：D7 の実際の接続射の計算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded DGNerve SSet
open scoped Simplicial ZeroObject
variable {S : Type u} [CommRing S] {X Y : Semifree S}

/-- 両端を Semifree の包含像に合わせた周囲の cofiber 比較射。 -/
def cofiberSuspensionHomOnInclusion (f : X.val ⟶ Y.val) :
    (SSet.HomotopyCategory.mk
      (functorVertex ((semifreeCofiberZeroTriangle f).square ≫ derivedInfinityInclusion)) :
        hoFunctor.obj ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj (dgNerve S (Complex S)))) ⟶
      SSet.HomotopyCategory.mk
        (functorVertex ((semifreeSuspensionSquare X).square ≫ derivedInfinityInclusion)) :=
  chosenEqToHom (congrArg (fun F => SSet.HomotopyCategory.mk (functorVertex F))
      (semifreeCofiberZeroTriangle_inclusion f)) ≫
    cofiberToSuspensionSquareHom f ≫
      chosenEqToHom (congrArg (fun F => SSet.HomotopyCategory.mk (functorVertex F))
        (semifreeSuspensionSquare_inclusion X).symm)

/-- Semifree 内の cofiber 四角形から標準 suspension 四角形への実際の図式射。 -/
def semifreeCofiberSuspensionHom (f : X.val ⟶ Y.val) :
    (SSet.HomotopyCategory.mk (functorVertex (semifreeCofiberZeroTriangle f).square) :
      hoFunctor.obj ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj (derivedInfinityCategory S))) ⟶
      SSet.HomotopyCategory.mk (functorVertex (semifreeSuspensionSquare X).square) :=
  Classical.choose (exists_fullInclusion_functorHom S (Complex S) (complexSemifree S)
    (semifreeCofiberZeroTriangle f).square (semifreeSuspensionSquare X).square
    (cofiberSuspensionHomOnInclusion f))

/-- 持ち上げた比較射の包含像は周囲で構成した二段比較。 -/
lemma semifreeCofiberSuspensionHom_inclusion_arrow (f : X.val ⟶ Y.val) :
    Arrow.mk ((hoFunctor.map ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map
      derivedInfinityInclusion)).toFunctor.map (semifreeCofiberSuspensionHom f)) =
      Arrow.mk (cofiberSuspensionHomOnInclusion f) :=
  Classical.choose_spec (exists_fullInclusion_functorHom S (Complex S) (complexSemifree S)
    (semifreeCofiberZeroTriangle f).square (semifreeSuspensionSquare X).square
    (cofiberSuspensionHomOnInclusion f))

end SerrePositivity.InfinityCategories
