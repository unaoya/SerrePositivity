module
public import SerrePositivity.KST.ProExcision.IntegerUnitizationIdealIso
public import SerrePositivity.KST.Comparison.DoldKanGL

/-!
# 非単位単体環の一般線形モノイド

概要：整数単位化の ĜL 内で整数成分が恒等行列となる部分モノイドを構成する。
方針：π₀ での可逆性と整数射影の核条件を独立に保持する。
規約：KST §4.3、Claim 4.15、正本 §13-10。各次数で可逆とは要求しない。
使われ方：Lemma 4.16 の実三角ブロック群を一般線形モノイドへ比較する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial

/-- 概要：π₀ で可逆かつ整数成分が恒等行列である行列の部分モノイド。
方針：整数成分の環準同型による単位元の逆像を ĜL と交わす。
規約：KST Claim 4.15 の非単位環の ĜL。次数ごとの逆行列はデータに含めない。
使われ方：非単位環の一般線形単体的モノイドの各次数。 -/
def NonUnitalSimplicialRing.hatGLSubmonoid (I : NonUnitalSimplicialRing.{u})
    (n q : ℕ) : Submonoid (Matrix (Fin n) (Fin n) (Unitization ℤ (I.obj (op ⦋q⦌)))) where
  carrier := {M | M ∈ Comparison.hatGLSubmonoid I.standardIdeal.ambient n q ∧
    (Unitization.fstHom ℤ (I.obj (op ⦋q⦌))).mapMatrix M = 1}
  one_mem' := ⟨Submonoid.one_mem _, map_one _⟩
  mul_mem' := by
    intro A B hA hB
    exact ⟨Submonoid.mul_mem _ hA.1 hB.1, by rw [map_mul, hA.2, hB.2, one_mul]⟩

/-- 概要：整数射影は非単位環準同型の単位化と可換。
方針：整数成分を保つ標準拡張の公式を使う。
規約：KST Claim 4.15 の係数方向の自然性。
使われ方：面・退化が ĜL の整数核条件を保つことの証明。 -/
lemma integerUnitizationMap_fst_matrix {J K : Type u} [NonUnitalRing J] [NonUnitalRing K]
    (f : J →ₙ+* K) {n : ℕ} (M : Matrix (Fin n) (Fin n) (Unitization ℤ J)) :
    (Unitization.fstHom ℤ K).mapMatrix ((integerUnitizationMap f).mapMatrix M) =
      (Unitization.fstHom ℤ J).mapMatrix M := by
  ext i j
  exact integerUnitizationMap_fst f (M i j)

/-- 概要：非単位環の ĜL の面・退化。
方針：周囲の ĜL の面・退化と整数核条件の保存を組み合わせる。
規約：KST Claim 4.15、任意の単体射を許す。
使われ方：ĜL を実単体的モノイドに束ねる。 -/
def NonUnitalSimplicialRing.hatGLPullback (I : NonUnitalSimplicialRing.{u})
    (n : ℕ) {p q : ℕ} (f : ⦋p⦌ ⟶ ⦋q⦌) :
    I.hatGLSubmonoid n q →* I.hatGLSubmonoid n p where
  toFun M := ⟨(integerUnitizationMap (I.map f.op)).mapMatrix M.val, by
    constructor
    · exact (Comparison.hatGLPullback I.standardIdeal.ambient n f ⟨M.val, M.property.1⟩).property
    · rw [integerUnitizationMap_fst_matrix]
      exact M.property.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' A B := Subtype.ext (map_mul _ A.val B.val)

/-- 概要：非単位単体環の一般線形単体的モノイド。
方針：π₀ での可逆性と整数核条件を保つ実写像を束ねる。
規約：KST Claim 4.15。群状性は定義に仮定しない。
使われ方：相対 bar ホモロジーの実比較射の対象。 -/
def NonUnitalSimplicialRing.hatGL (I : NonUnitalSimplicialRing.{u}) (n : ℕ) :
    SimplicialObject MonCat.{u} where
  obj k := MonCat.of (I.hatGLSubmonoid n k.unop.len)
  map f := MonCat.ofHom (I.hatGLPullback n f.unop)
  map_id k := by
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro M
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    change integerUnitizationMap (I.map (𝟙 k)) (M.val i j) = M.val i j
    rw [I.map_id, integerUnitizationMap_id]
    rfl
  map_comp f g := by
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro M
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    change integerUnitizationMap (I.map (f ≫ g)) (M.val i j) =
      integerUnitizationMap (I.map g) (integerUnitizationMap (I.map f) (M.val i j))
    rw [I.map_comp, integerUnitizationMap_comp]
    rfl

/-- 概要：非単位環の ĜL から周囲の全行列モノイドへの実表現。
方針：各次数で部分モノイドの包含を使う。
規約：KST Lemma 4.16 と Claim 4.15 の外部作用。
使われ方：全行列同変な実ホモトピーの作用制限。 -/
def NonUnitalSimplicialRing.hatGLRepresentation (I : NonUnitalSimplicialRing.{u}) (n : ℕ) :
    I.hatGL n ⟶ I.standardIdeal.matrixMonoid n where
  app k := MonCat.ofHom (I.hatGLSubmonoid n k.unop.len).subtype
  naturality {k l} f := by
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro M
    rfl

end SerrePositivity.KST.ProExcision
