module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Coalgebra
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Commutative
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Morphism
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.UnitPowers
public import SerrePositivity.HomotopicalAlgebra.Complexes.ProjectiveModel

/-!
模型。文献の定義との比較は後で
# E-coalgebra 区間の抽象界面

概要：Berger–Moerdijk 命題 4.1・§4.6.3、Berger–Fresse §3.1 の余代数区間を記述する。
方針：実際の余代数、二端点と収縮、その余演算の可換図式を持つ。
規約：端点の和からの射に射影 cofibration、収縮に擬同型を要求する。
使われ方：convolution の端点・定数射を作り、path object による右転送を証明する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}

/-- 概要：augmentation により単位対象に指定される n 出力の余演算（BF §3.1）。
方針：係数を余単位へ送り、単位を n 重テンソルへ展開する。
規約：n=0 の展開は恒等射である。
使われ方：区間の端点・収縮の余演算保存を明示的な可換図式で述べる。 -/
def unitCoaction (ε : P ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.commutativeOperad A) (n : ℕ) :
    P.arity n ⊗ (𝟙_ (Complex A)) ⟶ power (𝟙_ (Complex A)) n :=
  (ε.map.app (_root_.SerrePositivity.FiniteBijection.of n) ▷ (𝟙_ (Complex A))) ≫
    (λ_ (𝟙_ (Complex A))).hom ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso (Complex A) n).inv

/-- 概要：augmentation を持つオペラッドの余代数区間（BM 命題 4.1、BF §3.1）。
方針：余演算を保つ端点・収縮で単位の cylinder を与える。
規約：モデル構造・path object・転送の存在を構造の入力に含めない。
使われ方：任意の P 代数の functorial path object を convolution で構成する。 -/
structure CoalgebraInterval (ε : P ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.commutativeOperad A) where
  /-- 概要：区間の P-coalgebra（BF §3.1）。
  方針：単なる複体に加えて単位・等変性・合成則を満たす全余演算を持つ。
  規約：arity 0 の余演算も含む。
  使われ方：Hom(H,B) の演算の評価点を分配する。 -/
  coalgebra : P.Coalgebra
  /-- 概要：区間の二つの端点（BM 命題 4.1）。
  方針：テンソル単位からの二つの chain map を与える。
  規約：false を始点、true を終点とする。
  使われ方：Hom(H,B) から二つの B への評価を誘導する。 -/
  endpoint (b : Bool) : 𝟙_ (Complex A) ⟶ coalgebra.carrier
  /-- 概要：区間から単位への収縮（BM 命題 4.1）。
  方針：複体の射として与える。
  規約：微分と可換であり全ての余演算を保つ。
  使われ方：B から Hom(H,B) への定数射を誘導する。 -/
  contraction : coalgebra.carrier ⟶ 𝟙_ (Complex A)
  /-- 概要：両端点の後の収縮は恒等射（BM 命題 4.1）。
  方針：単位の cylinder の三角形の可換性を要求する。
  規約：両端点で同じ収縮を使う。
  使われ方：path object の定数射と評価射の合成を計算する。 -/
  endpoint_contraction (b : Bool) : endpoint b ≫ contraction = 𝟙 _
  /-- 概要：端点は余演算を保つ（BF §3.1）。
  方針：単位上の明示的な余演算と各出力への端点で比較する。
  規約：augmentation に由来する単位上の余演算を使う。
  使われ方：端点評価が P 代数射となることを証明する。 -/
  endpoint_coaction (b : Bool) (n : ℕ) :
    (P.arity n ◁ endpoint b) ≫ coalgebra.coaction n =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.unitCoaction ε n ≫ _root_.SerrePositivity.TensorPowers.map (endpoint b) n
  /-- 概要：収縮は余演算を保つ（BF §3.1）。
  方針：各出力への収縮と余演算の前の収縮で比較する。
  規約：端点条件と同じ単位上の余演算を使う。
  使われ方：定数射が P 代数射となることを証明する。 -/
  contraction_coaction (n : ℕ) :
    coalgebra.coaction n ≫ _root_.SerrePositivity.TensorPowers.map contraction n =
      (P.arity n ◁ contraction) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.unitCoaction ε n
  /-- 概要：二端点からの包含は射影 cofibration（BM 命題 4.1）。
  方針：具体的な生成 cofibration の右持ち上げクラスに対する左持ち上げ性で述べる。
  規約：Ch(A) のモデル構造の instance は要求しない。
  使われ方：二端点への評価が全ての次数で全射となることを証明する。 -/
  boundary_cofibration : (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A).rlp.llp
    (biprod.desc (endpoint false) (endpoint true))
  /-- 概要：区間の収縮は擬同型（BM 命題 4.1）。
  方針：既存の複体の擬同型という具体的な性質を要求する。
  規約：転送先の弱同値やモデル構造を仮定しない。
  使われ方：定数射が底での擬同型となることを証明する。 -/
  contraction_quasiIso : QuasiIso contraction

namespace CoalgebraInterval

variable {ε : P ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.commutativeOperad A} (I : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval ε)

/-- 概要：二端点の和から区間への包含（BM 命題 4.1）。
方針：複体の二項直和からの余積射を用いる。
規約：始点を左、終点を右とする。
使われ方：区間の底の cylinder 分解を記述する。 -/
def boundary : (𝟙_ (Complex A)) ⊞ (𝟙_ (Complex A)) ⟶ I.coalgebra.carrier :=
  biprod.desc (I.endpoint false) (I.endpoint true)

/-- 概要：二端点から収縮への合成は二つの恒等射の和（BM 命題 4.1）。
方針：二項直和の包含との合成で検査する。
規約：単位対象の fold 射として述べる。
使われ方：底の複体での cylinder 分解の可換性を供給する。 -/
lemma boundary_contraction : I.boundary ≫ I.contraction = biprod.desc (𝟙 _) (𝟙 _) := by
  apply biprod.hom_ext'
  · simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.boundary, biprod.inl_desc_assoc, I.endpoint_contraction, biprod.inl_desc]
  · simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.boundary, biprod.inr_desc_assoc, I.endpoint_contraction, biprod.inr_desc]


/-- 概要：区間の両端点は擬同型である（BM 命題 4.1）。
方針：端点の後の収縮が恒等射であり収縮が擬同型であることから二対三性を使う。
規約：モデル構造の instance を用いない。
使われ方：定数射と端点評価の弱同値性を検査する。 -/
lemma endpoint_quasiIso (b : Bool) : QuasiIso (I.endpoint b) := by
  let := I.contraction_quasiIso
  have : QuasiIso (I.endpoint b ≫ I.contraction) := by
    rw [I.endpoint_contraction]
    infer_instance
  exact quasiIso_of_comp_right (I.endpoint b) I.contraction

end CoalgebraInterval

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
