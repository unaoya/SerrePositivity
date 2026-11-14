module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceRightKan
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：左 pinched 写像空間と左右のホモトピー圏の射の反転の比較。
方針：右模型を単体集合とパラメータの両方で反転する。
規約：左模型は最初の頂点を x、残りの面を y に定値とする向き。
使われ方：Kerodon Proposition 4.6.5.5（Tag 01L0）、HTT §1.2.2–1.2.3。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet SSet.Truncated
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：反転した単体集合の辺を元の向きへ戻す。
方針：一単体を opObjEquiv で戻し、両端を交換する。
規約：元の X を型引数で指定する。
使われ方：Kerodon §4.6.5（Tag 01KW）、反転したホモトピー圏の射の比較。 -/
def edgeUnop {X : SSet.{u}} {x y : X.op _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X.op) x y) :
    SSet.Truncated.Edge (X := (truncation 2).obj X)
      (SSet.opObjEquiv y) (SSet.opObjEquiv x) where
  edge := SSet.opObjEquiv e.edge
  src_eq := by
    change X.δ 1 (SSet.opObjEquiv e.edge) = _
    rw [SSet.δ_opObjEquiv]
    exact congrArg SSet.opObjEquiv e.tgt_eq
  tgt_eq := by
    change X.δ 0 (SSet.opObjEquiv e.edge) = _
    rw [SSet.δ_opObjEquiv]
    exact congrArg SSet.opObjEquiv e.src_eq

/-- 概要：辺の反転とその逆は同値を与える。
方針：二つの一単体の同値を逆向きに使う。
規約：二頂点間の辺の型全体の同値。
使われ方：Kerodon §4.6.5（Tag 01KW） の左右の模型の零単体の比較。 -/
def edgeOpEquiv {X : SSet.{u}} (x y : X _⦋0⦌) :
    SSet.Truncated.Edge (X := (truncation 2).obj X) x y ≃
      SSet.Truncated.Edge (X := (truncation 2).obj X.op)
        (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x) where
  toFun := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp
  invFun := edgeUnop (X := X)
  left_inv _ := SSet.Truncated.Edge.ext rfl
  right_inv _ := SSet.Truncated.Edge.ext rfl

/-- 概要：辺の反転を戻す写像は恒等辺を保つ。
方針：零番目の退化の反転の式を使う。
規約：任意の X.op の頂点に適用できる。
使われ方：Kerodon §4.6.5（Tag 01KW） のホモトピー関係の反転。 -/
lemma edgeUnop_id {X : SSet.{u}} (x : X.op _⦋0⦌) :
    edgeUnop (X := X) (SSet.Truncated.Edge.id (X := (truncation 2).obj X.op) x) =
      SSet.Truncated.Edge.id (X := (truncation 2).obj X) (SSet.opObjEquiv x) := by
  apply SSet.Truncated.Edge.ext
  change SSet.opObjEquiv (X.op.σ 0 x) = X.σ 0 (SSet.opObjEquiv x)
  rw [SSet.op_σ]
  rfl

/-- 概要：反転した単体集合の三角形を元の逆順の合成三角形へ戻す。
方針：二単体を opObjEquiv で戻し、零番目と二番目の面を交換する。
規約：quasicategory 性は不要。
使われ方：Kerodon §4.6.5（Tag 01KW）、左右のホモトピー関係の比較。 -/
def compStructUnop {X : SSet.{u}} {x y z : X.op _⦋0⦌}
    {f : SSet.Truncated.Edge (X := (truncation 2).obj X.op) x y}
    {g : SSet.Truncated.Edge (X := (truncation 2).obj X.op) y z}
    {h : SSet.Truncated.Edge (X := (truncation 2).obj X.op) x z}
    (t : SSet.Truncated.Edge.CompStruct f g h) :
    SSet.Truncated.Edge.CompStruct (edgeUnop (X := X) g) (edgeUnop (X := X) f)
      (edgeUnop (X := X) h) where
  simplex := SSet.opObjEquiv t.simplex
  d₂ := by
    change X.δ 2 (SSet.opObjEquiv t.simplex) = SSet.opObjEquiv g.edge
    rw [SSet.δ_opObjEquiv]
    exact congrArg SSet.opObjEquiv t.d₀
  d₀ := by
    change X.δ 0 (SSet.opObjEquiv t.simplex) = SSet.opObjEquiv f.edge
    rw [SSet.δ_opObjEquiv]
    exact congrArg SSet.opObjEquiv t.d₂
  d₁ := by
    change X.δ 1 (SSet.opObjEquiv t.simplex) = SSet.opObjEquiv h.edge
    rw [SSet.δ_opObjEquiv]
    exact congrArg SSet.opObjEquiv t.d₁

/-- 概要：反転した二辺の左ホモトピーと元の二辺の左ホモトピーは同値。
方針：三角形の反転は左右のホモトピーを交換し、quasicategory では両者が一致する。
規約：元の X の quasicategory 性だけを仮定する。
使われ方：HTT §1.2.3、Kerodon §4.6.5（Tag 01KW） の辺の類の比較。 -/
lemma homotopicL_edgeOp_iff {X : SSet.{u}} [Quasicategory X] {x y : X _⦋0⦌}
    (f g : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) :
    SSet.Truncated.HomotopicL (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp g) ↔ SSet.Truncated.HomotopicL f g := by
  constructor
  · rintro ⟨t⟩
    have h : SSet.Truncated.HomotopicR f g := by
      constructor
      have ht := compStructUnop (X := X) t
      rw [edgeUnop_id] at ht
      exact ht
    exact h.homotopicL
  · rintro ⟨t⟩
    have h : SSet.Truncated.HomotopicR (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp g) := by
      constructor
      have ht := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.compStructOp t
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp_id] at ht
      exact ht
    exact h.homotopicL

/-- 概要：辺の類によるホモトピー圏の Hom は反転した Hom と同値。
方針：辺の同値とホモトピー関係の同値を商に降ろす。
規約：反転後の二頂点の順序は y,x。
使われ方：HTT §1.2.3、Kerodon §4.6.5（Tag 01KW） の左模型の π₀ の比較。 -/
noncomputable def homotopyCategory₂OpHomEquiv {X : SSet.{u}} [Quasicategory X]
    (x y : X _⦋0⦌) :
    (HomotopyCategory₂.mk (A := (truncation 2).obj X) x ⟶ HomotopyCategory₂.mk y) ≃
      (HomotopyCategory₂.mk (A := (truncation 2).obj X.op) (SSet.opObjEquiv.symm y) ⟶
        HomotopyCategory₂.mk (SSet.opObjEquiv.symm x)) :=
  Quotient.congr (edgeOpEquiv x y) (fun f g ↦ (homotopicL_edgeOp_iff f g).symm)

/-- 概要：通常のホモトピー圏の Hom は反転した単体集合の逆向きの Hom と同値。
方針：A1 の比較同値で辺の類の同値を両側から挟む。
規約：quasicategory X の任意の二頂点を扱う。
使われ方：HTT §1.2.3、Kerodon §4.6.5（Tag 01KW） の左模型の π₀ の型。 -/
noncomputable def homotopyCategoryOpHomEquiv {X : SSet.{u}} [Quasicategory X]
    (x y : X _⦋0⦌) :
    (SSet.HomotopyCategory.mk x ⟶ SSet.HomotopyCategory.mk y) ≃
      ((SSet.HomotopyCategory.mk (SSet.opObjEquiv.symm y) : hoFunctor.obj X.op) ⟶
        SSet.HomotopyCategory.mk (SSet.opObjEquiv.symm x)) :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyCategoryBridge X).fullyFaithfulFunctor.homEquiv
    (X := HomotopyCategory₂.mk (A := (truncation 2).obj X) x)
    (Y := HomotopyCategory₂.mk (A := (truncation 2).obj X) y)).symm.trans
      ((homotopyCategory₂OpHomEquiv x y).trans
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyCategoryBridge X.op).fullyFaithfulFunctor.homEquiv
          (X := HomotopyCategory₂.mk (A := (truncation 2).obj X.op) (SSet.opObjEquiv.symm y))
          (Y := HomotopyCategory₂.mk (A := (truncation 2).obj X.op) (SSet.opObjEquiv.symm x))))

/-- 概要：反転した単体集合の連結成分から元の連結成分への写像。
方針：頂点を opObjEquiv で戻し、逆向きになる辺の連結成分の等式を使う。
規約：quasicategory 性は不要。
使われ方：Kerodon §4.6.5（Tag 01KW） の左模型のパラメータの反転。 -/
def piZeroOpToPiZero (X : SSet.{u}) : SSet.π₀ X.op → SSet.π₀ X :=
  SSet.π₀.lift (fun x ↦ SSet.π₀.mk (SSet.opObjEquiv x))
    (fun _ _ e ↦ (SSet.π₀.sound (SSet.Edge.ofTruncated (edgeUnop (X := X) e.toTruncated))).symm)

/-- 概要：元の単体集合の連結成分を反転した単体集合の連結成分へ送る。
方針：頂点を opObjEquiv の逆で写し、辺の向きの交換を使う。
規約：quasicategory 性は不要。
使われ方：Kerodon §4.6.5（Tag 01KW） の反転した連結成分の逆写像。 -/
def piZeroToPiZeroOp (X : SSet.{u}) : SSet.π₀ X → SSet.π₀ X.op :=
  SSet.π₀.lift (fun x ↦ SSet.π₀.mk (SSet.opObjEquiv.symm x))
    (fun _ _ e ↦ (SSet.π₀.sound (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp e.toTruncated))).symm)

/-- 概要：単体集合とその反転の連結成分は同値。
方針：各零単体の連結成分で二つの写像の合成を計算する。
規約：任意の単体集合で成立する。
使われ方：Kerodon §4.6.5（Tag 01KW） の左模型の π₀。 -/
def piZeroOpEquiv (X : SSet.{u}) : SSet.π₀ X.op ≃ SSet.π₀ X where
  toFun := piZeroOpToPiZero X
  invFun := piZeroToPiZeroOp X
  left_inv a := by
    obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective a
    rfl
  right_inv a := by
    obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective a
    rfl

/-- 概要：左 pinched 写像空間。
方針：反転した X の右模型をパラメータでも反転する。
規約：最初の頂点は x、残りの面は y に定値となる向き。
使われ方：Kerodon Construction 4.6.5.1（Tag 01KX） の左模型。 -/
@[kerodon 01KX]
def pinchedHomLeft {X : SSet.{u}} (x y : X _⦋0⦌) : SSet.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := X.op) (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x)).op

/-- 概要：quasicategory の左 pinched 写像空間は Kan 複体。
方針：右模型の Kan 性を二つの反転に沿って移す。
規約：仮定は元の X の quasicategory 性だけ。
使われ方：Kerodon Proposition 4.6.5.5（Tag 01L0） の左模型。 -/
@[kerodon 01L0]
instance pinchedHomLeft_kanComplex {X : SSet.{u}} [Quasicategory X] (x y : X _⦋0⦌) :
    KanComplex (pinchedHomLeft x y) := by
  change KanComplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := X.op)
    (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x)).op)
  infer_instance

/-- 概要：左 pinched 写像空間の連結成分は元のホモトピー圏の Hom と同値。
方針：パラメータの反転、右模型の π₀、ホモトピー圏の反転の Hom 同値を合成する。
規約：右辺の射の向きは x から y。
使われ方：HTT §1.2.2–1.2.3、Kerodon §4.6.5（Tag 01KW） の左模型。 -/
noncomputable def pinchedHomLeftPiZeroEquiv {X : SSet.{u}} [Quasicategory X]
    (x y : X _⦋0⦌) : SSet.π₀ (pinchedHomLeft x y) ≃
      (SSet.HomotopyCategory.mk x ⟶ SSet.HomotopyCategory.mk y) :=
  (piZeroOpEquiv _).trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomPiZeroEquiv (X := X.op) (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x)).trans
      (homotopyCategoryOpHomEquiv x y).symm)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "1.2.2.5"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft
attribute [cite HTT "1.2.3.6"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homotopicL_edgeOp_iff
