module

public import SerrePositivity.EInfinity.BarrattEccles.DerivedPullback

/-!
# E 代数の homotopy 引き戻しを底の複体で計算する

概要：BM 命題 4.1・Hovey §1.3 の導来引き戻しを同じ置換で底でも計算する。
方針：E 代数の左脚置換は底でも擬同型と fibration であり、忘却は引き戻しを保つ。
規約：具体的な二つのモデル構造を局所的に選ぶ。基礎環は任意の可換環。
使われ方：E2a-4 の底での homotopy 引き戻しと E2b の導来忘却。
-/

@[expose] public section

noncomputable section

universe u v w v' w'

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits HomotopicalAlgebra
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：底の複体の固定右脚との引き戻し関手（Hovey §1.3）。
方針：複体の slice の基底変換の後で底を取る。
規約：非有界整数複体。
使われ方：E 代数で選んだ置換を底の右導来計算に用いる。 -/
def carrierPullbackFunctor {Y Z : Complex A} (g : Y ⟶ Z) : Over Z ⥤ Complex A :=
  Over.pullback g ⋙ Over.forget Y

/-- 概要：底の引き戻し関手は射影モデル構造で右 Quillen（Hovey §1.3）。
方針：fibration と trivial fibration の基底変換安定性を使う。
規約：具体的な射影モデル構造を局所的に選ぶ。
使われ方：底の homotopy 引き戻しの導来構成。 -/
lemma carrierPullbackFunctor_isRightQuillen {Y Z : Complex A} (g : Y ⟶ Z) :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    SerrePositivity.Quillen.IsRightQuillen (carrierPullbackFunctor A g) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  constructor
  · intro X X' f hf
    exact (fibrations (Complex A)).overPullbackMap g f hf
  · intro X X' f hf
    exact (trivialFibrations (Complex A)).overPullbackMap g f hf

/-- 概要：E 代数の左脚置換の底を複体の slice 対象にする（BM 命題 4.1）。
方針：置換の射影の底の複体射を取る。
規約：忘却後の基底を固定する。
使われ方：同じ置換による底の導来引き戻しの計算。 -/
def carrierReplacementOver {X Z : (operad A).Algebra} (f : X ⟶ Z) : Over Z.carrier :=
  Over.mk (fibrationReplacement A f).p.hom

/-- 概要：底の左脚から同じ置換への包含（BM 命題 4.1）。
方針：代数射の分解三角形を底の複体へ移す。
規約：底の基底は恒等で固定する。
使われ方：底の局所化における元の左脚との比較。 -/
def carrierReplacementInclusion {X Z : (operad A).Algebra} (f : X ⟶ Z) :
    Over.mk f.hom ⟶ carrierReplacementOver A f :=
  Over.homMk (fibrationReplacement A f).i.hom
    (congrArg (fun h => h.hom) (fibrationReplacement A f).fac)

/-- 概要：同じ置換は底の slice でも弱同値（BM 命題 4.1）。
方針：包含の擬同型性と射影モデル構造の弱同値判定を使う。
規約：底の射影モデル構造は局所的に選ぶ。
使われ方：底での導来引き戻しの元の左脚への比較。 -/
lemma carrierReplacementInclusion_weakEquivalence {X Z : (operad A).Algebra}
    (f : X ⟶ Z) :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    WeakEquivalence (carrierReplacementInclusion A f) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  change WeakEquivalence (carrierReplacementInclusion A f)
  apply (weakEquivalences_over_iff Z.carrier _).mpr
  exact ⟨fibrationReplacement_quasiIso A f⟩

/-- 概要：同じ置換は底の slice でも fibrant（BM 命題 4.1）。
方針：置換射影の全次数全射性を slice の終対象への fibration に移す。
規約：代数の置換を再度選び直さない。
使われ方：忘却後の導来比較同型が存在する計算点。 -/
lemma carrierReplacementOver_isFibrant {X Z : (operad A).Algebra} (f : X ⟶ Z) :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    IsFibrant (carrierReplacementOver A f) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  change IsFibrant (carrierReplacementOver A f)
  apply (isFibrant_iff_of_isTerminal
    ((Over.mkIdTerminal (X := Z.carrier)).from (carrierReplacementOver A f))
    (Over.mkIdTerminal (X := Z.carrier))).mpr
  rw [fibrations_over_iff, Over.mkIdTerminal_from_left]
  exact ⟨fibrationReplacement_surjective A f⟩

/-- 概要：E 代数の homotopy 引き戻しは底の右導来引き戻しも計算する（Hovey §1.3）。
方針：底の引き戻し比較、fibrant 点での導来比較、包含の局所化同型を合成する。
規約：底の二つの局所化と右導来関手は任意。モデル構造の入力仮定なし。
使われ方：E2a-4 の homotopy 引き戻しを底の複体で計算する。 -/
def homotopyPullbackCarrierDerivedIso {X Y Z : (operad A).Algebra}
    (f : X ⟶ Z) (g : Y ⟶ Z)
    {H : Type w} [Category.{v} H] {S : Type w'} [Category.{v'} S]
    (Q : Complex A ⥤ H) (L : Over Z.carrier ⥤ S) (RF : S ⥤ H)
    (β : carrierPullbackFunctor A g.hom ⋙ Q ⟶ L ⋙ RF) :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    ∀ [Q.IsLocalization (weakEquivalences (Complex A))]
      [L.IsLocalization (weakEquivalences (Over Z.carrier))],
      RF.IsRightDerivedFunctor β (weakEquivalences (Over Z.carrier)) →
      (Q.obj (homotopyPullback A f g).carrier ≅ RF.obj (L.obj (Over.mk f.hom))) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  dsimp only
  intro hQ hL hRF
  have := hQ
  have := hL
  have := hRF
  have := carrierPullbackFunctor_isRightQuillen A g.hom
  have := carrierReplacementOver_isFibrant A f
  have := carrierReplacementInclusion_weakEquivalence A f
  have := SerrePositivity.Quillen.rightComparison_isIso Q L β (carrierReplacementOver A f)
  have := Localization.inverts L (weakEquivalences (Over Z.carrier))
    (carrierReplacementInclusion A f) (mem_weakEquivalences _)
  exact (Q.mapIso (homotopyPullbackCarrierIso A f g)).trans
    ((asIso (β.app (carrierReplacementOver A f))).trans
      (RF.mapIso (asIso (L.map (carrierReplacementInclusion A f)))).symm)

end SerrePositivity.EInfinity.BarrattEccles
