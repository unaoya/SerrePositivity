module
public import SerrePositivity.KST.ProExcision.IntegerUnitizationComponents
public import SerrePositivity.KST.Comparison.MonoidComponents

/-!
# 非単位環の一般線形モノイドの成分比較

概要：整数核の ĜL の連結成分を成分環上の一般線形群へ単射で比較する。
方針：係数の辺を行列の辺へまとめ、整数成分が始点と一致することから核内へ制限する。
規約：KST Claim 4.15、各次数の逆元を仮定しない。
使われ方：逆成分の代表を持ち上げた後の群状性の検証。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite SSet
open scoped Simplicial

/-- 概要：非単位環の ĜL から標準単位化の ĜL への実包含。
方針：整数核条件を忘れる各次数の準同型を束ねる。
規約：KST Claim 4.15。使われ方：既存の成分比較への自然な接続。 -/
def NonUnitalSimplicialRing.hatGLAmbientMap (I : NonUnitalSimplicialRing.{u}) (n : ℕ) :
    I.hatGL n ⟶ Comparison.hatGLMonoidObject I.standardIdeal.ambient n where
  app k := MonCat.ofHom
    { toFun := fun a ↦ ⟨a.val, a.property.1⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  naturality {k l} f := by
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro a
    rfl

/-- 概要：整数核の ĜL の係数の辺を核内の行列の辺にまとめる。
方針：既存の周囲の辺の整数射影を始点の射影に同定する。
規約：KST Claim 4.15。使われ方：成分比較の単射性。 -/
def NonUnitalSimplicialRing.hatGLEdgeOfCoefficients
    (I : NonUnitalSimplicialRing.{u}) (n : ℕ) (a b : I.hatGLSubmonoid n 0)
    (e : ∀ i j : Fin n, (Comparison.ringSpace I.standardIdeal.ambient).Edge
      (a.val i j) (b.val i j)) :
    (Comparison.monoidSpace (I.hatGL n)).Edge a b := by
  let E := Comparison.hatGLEdgeOfCoefficients I.standardIdeal.ambient n
    ⟨a.val, a.property.1⟩ ⟨b.val, b.property.1⟩ e
  have hs := congrArg Subtype.val E.src_eq
  have ht := congrArg Subtype.val E.tgt_eq
  have hE : (Unitization.fstHom ℤ (I.obj (op ⦋1⦌))).mapMatrix E.edge.val = 1 := by
    rw [← integerUnitizationMap_fst_matrix (I.map (SimplexCategory.δ 1).op) E.edge.val]
    change (integerUnitizationMap (I.map (SimplexCategory.δ 1).op)).mapMatrix E.edge.val = a.val at hs
    rw [hs]
    exact a.property.2
  exact .mk ⟨E.edge.val, E.edge.property, hE⟩ (Subtype.ext hs) (Subtype.ext ht)

/-- 概要：整数核の ĜL の成分から成分環上の一般線形群への比較写像。
方針：実包含による π₀ の写像の後に既存の成分単元を取る。
規約：KST Claim 4.15。使われ方：群状性の単射な比較。 -/
def NonUnitalSimplicialRing.hatGLClassMap (I : NonUnitalSimplicialRing.{u}) (n : ℕ) :
    π₀ (Comparison.monoidSpace (I.hatGL n)) →
      (Matrix (Fin n) (Fin n) (π₀ (Comparison.ringSpace I.standardIdeal.ambient)))ˣ :=
  Comparison.hatGLClassMap I.standardIdeal.ambient n ∘
    mapπ₀ (Functor.whiskerRight (I.hatGLAmbientMap n) (forget MonCat))

/-- 概要：成分比較を零次の行列で評価する公式。
方針：商への包含と既存の成分比較の定義を展開する。
規約：KST Claim 4.15。使われ方：実行列積と成分単元の積の照合。 -/
lemma NonUnitalSimplicialRing.hatGLClassMap_mk
    (I : NonUnitalSimplicialRing.{u}) (n : ℕ) (a : I.hatGLSubmonoid n 0) :
    I.hatGLClassMap n (π₀.mk a) =
      Comparison.hatGLVertexUnit I.standardIdeal.ambient n ⟨a.val, a.property.1⟩ := rfl

/-- 概要：整数核の成分比較は単射。
方針：成分行列の一致から係数の辺を選び、整数核内の一本の辺にまとめる。
規約：KST Claim 4.15、Kan 性や次数ごとの可逆性は不要。
使われ方：成分環で検証した積の等式を核内の π₀ へ戻す。 -/
lemma NonUnitalSimplicialRing.hatGLClassMap_injective
    (I : NonUnitalSimplicialRing.{u}) (n : ℕ) : Function.Injective (I.hatGLClassMap n) := by
  intro x y h
  induction x using π₀.rec with | mk a => ?_
  induction y using π₀.rec with | mk b => ?_
  have hm : Comparison.matrixToComponents I.standardIdeal.ambient n 0 a.val =
      Comparison.matrixToComponents I.standardIdeal.ambient n 0 b.val := by
    have hv := congrArg Units.val h
    change (a.property.1.unit : Matrix (Fin n) (Fin n)
      (π₀ (Comparison.ringSpace I.standardIdeal.ambient))) =
      (b.property.1.unit : Matrix (Fin n) (Fin n)
        (π₀ (Comparison.ringSpace I.standardIdeal.ambient))) at hv
    simpa only [IsUnit.unit_spec] using hv
  have he : ∀ i j : Fin n, Nonempty ((Comparison.ringSpace I.standardIdeal.ambient).Edge
      (a.val i j) (b.val i j)) := by
    intro i j
    apply Comparison.SimplicialRing.nonempty_edge_of_mk_eq I.standardIdeal.ambient
    simpa only [Comparison.matrixToComponents_zero_entry] using congrArg (fun M ↦ M i j) hm
  exact π₀.sound (I.hatGLEdgeOfCoefficients n a b (fun i j ↦ Classical.choice (he i j)))

end SerrePositivity.KST.ProExcision
