module

public import SerrePositivity.KST.Comparison.CoconeOverBase
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-!
# 部分単体集合の二項の和の余錐

概要：交叉から二つの部分単体集合への span の余極限を、その和で具体的に与える。
方針：部分単体集合の束の bicartesian square と、固定対象との積の余極限保存を使う。
規約：Segal 1974 Proposition 1.6 の有限個の面の貼り合わせ。
使われ方：部分対象ごとのホモトピー引き戻し性の二項の和への移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
variable {K : SSet.{u}}

/--
概要：二つの部分単体集合とその交叉の span。
方針：交叉からの二つの包含を使う。
規約：中央は交叉、左右は指定した二つの部分対象。
使われ方：二項の和の余極限の添字図式。
-/
def subcomplexUnionSpan (U V : K.Subcomplex) : WalkingSpan ⥤ SSet.{u} :=
  span (SSet.Subcomplex.homOfLE (inf_le_left : U ⊓ V ≤ U))
    (SSet.Subcomplex.homOfLE (inf_le_right : U ⊓ V ≤ V))

/--
概要：二つの部分単体集合の和を頂点とする余錐。
方針：和への二つの包含を使う。
規約：全て同じ単体集合の部分対象として計算する。
使われ方：和の普遍性と固定対象との積。
-/
def subcomplexUnionCocone (U V : K.Subcomplex) : Cocone (subcomplexUnionSpan U V) :=
  PushoutCocone.mk (SSet.Subcomplex.homOfLE (le_sup_left : U ≤ U ⊔ V))
    (SSet.Subcomplex.homOfLE (le_sup_right : V ≤ U ⊔ V)) rfl

/--
概要：部分単体集合の和の余錐は余極限である。
方針：束の交叉と和の bicartesian square の実際の pushout を使う。
規約：一般の関係式の商ではなく部分対象の和の普遍性。
使われ方：有限被覆の二項の貼り合わせ。
-/
def subcomplexUnionCoconeIsColimit (U V : K.Subcomplex) :
    IsColimit (subcomplexUnionCocone U V) :=
  (SSet.Subcomplex.BicartSq.isPushout
    (⟨rfl, rfl⟩ : SSet.Subcomplex.BicartSq (U ⊓ V) U V (U ⊔ V))).isColimit

/--
概要：固定した左因子との積は単射を保つ。
方針：二つの射影で判定し、右の射影では元の単射を打ち消す。
規約：SSet の直積の具体的な選択を使わない普遍性の証明。
使われ方：積を取った交叉の包含の単射性。
-/
theorem tensorLeft_mono_of_mono (X : SSet.{u}) {U V : SSet.{u}} (q : U ⟶ V) [Mono q] :
    Mono (X ◁ q) := by
  constructor
  intro Z a b h
  apply CartesianMonoidalCategory.hom_ext
  · have hf := congrArg (fun t => t ≫ fst X V) h
    simpa only [Category.assoc, whiskerLeft_fst] using hf
  · apply (cancel_mono q).mp
    have hs := congrArg (fun t => t ≫ snd X V) h
    simpa only [Category.assoc, whiskerLeft_snd] using hs

/--
概要：部分単体集合の和の余錐に固定した左因子との積を取る。
方針：tensorLeft を余錐へ適用する。
規約：図式の三頂点全てに同じ固定因子を掛ける。
使われ方：パラメータを持つ有限被覆の比較。
-/
def tensorSubcomplexUnionCocone (X : SSet.{u}) (U V : K.Subcomplex) :
    Cocone (subcomplexUnionSpan U V ⋙ tensorLeft X) :=
  (tensorLeft X).mapCocone (subcomplexUnionCocone U V)

/--
概要：固定した左因子との積を取った和の余錐も余極限である。
方針：cartesian closed な前層圏の tensorLeft の余極限保存を使う。
規約：固定因子の Kan 性や可縮性は不要。
使われ方：固定射へのホモトピー引き戻しの貼り合わせへの入力。
-/
def tensorSubcomplexUnionCoconeIsColimit (X : SSet.{u}) (U V : K.Subcomplex) :
    IsColimit (tensorSubcomplexUnionCocone X U V) :=
  isColimitOfPreserves (tensorLeft X) (subcomplexUnionCoconeIsColimit U V)

end SerrePositivity.KST.Comparison
