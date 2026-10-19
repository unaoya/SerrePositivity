module

public import SerrePositivity.KST.Spectra.SimplicialCochainNormalization
public import SerrePositivity.KST.Spectra.NormalizedValueCochainComplex

/-!
概要：係数の元を値とする全単体の cochain と正規化のホモトピー比較。
方針：全単体の関数の余単体図式を作り、ULift ℤ からの Hom の係数表示を移す。
規約：任意の加法群係数を許す。
使われ方：Goerss–Jardine III §2、VIII §2。BG の非斉次群 cochain の比較。
-/

@[expose] public section

universe u

open CategoryTheory Opposite SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.SimplicialValueCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：全単体上の通常の係数値の関数群の余単体図式。
方針：単体集合の作用への前合成を各次数の射とする。
規約：退化単体への値は任意。
使われ方：Goerss–Jardine VIII §2。群 cochain の全単体による表示。 -/
def diagram (K : SSet.{u}) (M : AddCommGrpCat.{u}) : CosimplicialObject AddCommGrpCat.{u} where
  obj n := AddCommGrpCat.of (K.obj (op n) → M)
  map θ := AddCommGrpCat.ofHom {
    toFun a s := a (K.map θ.op s)
    map_zero' := rfl
    map_add' _ _ := rfl }
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro a
    funext s
    change a (K.map (𝟙 (op n)) s) = a s
    rw [K.map_id]
    rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro a
    funext s
    change a (K.map (g.op ≫ f.op) s) = a (K.map f.op (K.map g.op s))
    rw [K.map_comp]
    rfl

def coefficientEquiv (K : SSet.{u}) (M : AddCommGrpCat.{u}) (n : SimplexCategory) :
    (K.obj (op n) → (AddCommGrpCat.of (ULift.{u} ℤ) ⟶ M)) ≃+ (K.obj (op n) → M) where
  toFun a s := AddCommGrpCat.uliftZMultiplesAddEquiv M (a s)
  invFun a s := (AddCommGrpCat.uliftZMultiplesAddEquiv M).symm (a s)
  left_inv a := by funext s; exact (AddCommGrpCat.uliftZMultiplesAddEquiv M).symm_apply_apply _
  right_inv a := by funext s; exact (AddCommGrpCat.uliftZMultiplesAddEquiv M).apply_symm_apply _
  map_add' a b := by funext s; exact map_add (AddCommGrpCat.uliftZMultiplesAddEquiv M) _ _

/-- 概要：整数の単位係数の Hom の余単体 cochain と係数の元の図式は自然に同型。
方針：各座標で一の像を取り、単体作用への前合成と可換であることを確認する。
規約：全ての面と退化に自然。
使われ方：Goerss–Jardine III §2、VIII §2。係数表示と通常の cochain の複体の比較。 -/
def diagramIso (K : SSet.{u}) (M : AddCommGrpCat.{u}) :
    SimplicialHomCochains.diagram K (AddCommGrpCat.of (ULift.{u} ℤ)) M ≅ diagram K M :=
  NatIso.ofComponents (fun n ↦ AddEquiv.toAddCommGrpIso (coefficientEquiv K M n)) (fun _ ↦ by
    apply ConcreteCategory.hom_ext
    intro a
    funext s
    rfl)

def complex (K : SSet.{u}) (M : AddCommGrpCat.{u}) : CochainComplex AddCommGrpCat.{u} ℕ :=
  AlgebraicTopology.AlternatingCofaceMapComplex.obj (diagram K M)

def complexIso (K : SSet.{u}) (M : AddCommGrpCat.{u}) :
    SimplicialHomCochains.complex K (AddCommGrpCat.of (ULift.{u} ℤ)) M ≅ complex K M :=
  (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u}).mapIso (diagramIso K M)

/-- 概要：全単体の通常の係数値 cochain と正規化 cochain はホモトピー同値。
方針：全単体の Hom の係数表示を逆にし、正規化の同値と正規化後の値の表示に合成する。
規約：群の cohomology への比較や幾何的微分との一致は別途扱う。
使われ方：Goerss–Jardine III §2、VIII §2。非正規化群 cochain の消滅を移す界面。 -/
def normalizationHomotopyEquiv (K : SSet.{u}) (M : AddCommGrpCat.{u}) :
    HomotopyEquiv (complex K M) (NormalizedValueCochains.complex K M) :=
  (HomotopyEquiv.ofIso (complexIso K M).symm).trans
    ((SimplicialHomCochains.normalizationHomotopyEquiv
      K (AddCommGrpCat.of (ULift.{u} ℤ)) M).trans
      (HomotopyEquiv.ofIso (NormalizedValueCochains.complexIso K M)))

end

end SerrePositivity.KST.Spectra.SimplicialValueCochains
