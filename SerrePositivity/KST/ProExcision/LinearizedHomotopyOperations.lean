module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AugmentationHomotopy
public import SerrePositivity.KST.ProExcision.LinearizedEndpoints

/-!
# 線形な m 次ホモトピーの合成と移送

概要：m 次ホモトピーを加法で連結し、始域と終域の写像に沿って移す。
方針：中間射の定数区間写像を引き、端点の自然性で両端条件を移送する。
規約：KST Definition A.3、Construction A.5 の右辺の augmentation 補正。
非被約な C(H) を維持し、区間ホモトピーの連結を幾何的な連結可能性に依存させない。
使われ方：A.5 の厳密化・比較の合成、最後の μ の適用、Lemma 4.16 の共役比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial
variable {X Y : SSet.{u}} {D E : SimplicialObject (ModuleCat.{u} ℤ)}
variable {f g k : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X ⟶ D} {m : ℕ}

/-- 概要：射とそれ自身の m 次ホモトピー。
方針：射影に射を合成した定数区間写像を使う。
規約：KST Definition A.3、零次を含む。使われ方：比較の恒等部分。 -/
def LinearizedMHomotopy.refl (f : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X ⟶ D) (m : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy f f m where
  h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinderProjection X ≫ f
  h₀ _ _ := by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₀_projection_assoc]
  h₁ _ _ := by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₁_projection_assoc]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy export _root_.SerrePositivity.KST.ProExcision.LinearizedMHomotopy (refl)

/-- 概要：m 次ホモトピーの向きを逆転する。
方針：f+g の定数区間写像から元の区間写像を引く。
規約：KST Definition A.3 の線形区間。使われ方：A.5 の比較の逆向きの合成。 -/
def LinearizedMHomotopy.symm (H : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy f g m) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy g f m where
  h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinderProjection X ≫ (f + g) - H.h
  h₀ n hn := by
    simp only [Preadditive.comp_sub, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₀_projection_assoc,
      NatTrans.app_sub, NatTrans.app_add, H.h₀ n hn]
    abel
  h₁ n hn := by
    simp only [Preadditive.comp_sub, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₁_projection_assoc,
      NatTrans.app_sub, NatTrans.app_add, H.h₁ n hn]
    abel

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy export _root_.SerrePositivity.KST.ProExcision.LinearizedMHomotopy (symm)

/-- 概要：二つの m 次ホモトピーを連結する。
方針：二つの区間写像の和から中間射の定数区間写像を引く。
規約：KST A.5・Lemma 4.16、通常の線形な連結。
使われ方：厳密化と AW/shuffle の標準比較の合成。 -/
def LinearizedMHomotopy.trans (H : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy f g m)
    (K : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy g k m) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy f k m where
  h := H.h + K.h - _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinderProjection X ≫ g
  h₀ n hn := by
    simp only [Preadditive.comp_sub, Preadditive.comp_add, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₀_projection_assoc,
      NatTrans.app_sub, NatTrans.app_add, H.h₀ n hn, K.h₀ n hn]
    abel
  h₁ n hn := by
    simp only [Preadditive.comp_sub, Preadditive.comp_add, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₁_projection_assoc,
      NatTrans.app_sub, NatTrans.app_add, H.h₁ n hn, K.h₁ n hn]
    abel

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy export _root_.SerrePositivity.KST.ProExcision.LinearizedMHomotopy (trans)

/-- 概要：m 次ホモトピーを小さい範囲へ制限する。
方針：区間写像は保ち、両端条件の上限だけを弱める。
規約：KST Definition A.3。使われ方：異なる上限の比較の合成。 -/
def LinearizedMHomotopy.restrict (H : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy f g m) {n : ℕ} (hn : n ≤ m) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy f g n where
  h := H.h
  h₀ i hi := H.h₀ i (hi.trans hn)
  h₁ i hi := H.h₁ i (hi.trans hn)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy export _root_.SerrePositivity.KST.ProExcision.LinearizedMHomotopy (restrict)

/-- 概要：m 次ホモトピーは終域の線形写像で移送できる。
方針：区間写像に終域の写像を後合成する。
規約：KST A.5、最後に C(μ) を適用する操作。
使われ方：因子の積に値を持つ比較から C(H) の比較を得る。 -/
def LinearizedMHomotopy.postcomp (H : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy f g m) (p : D ⟶ E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy (f ≫ p) (g ≫ p) m where
  h := H.h ≫ p
  h₀ n hn := by
    rw [← Category.assoc, NatTrans.comp_app, H.h₀ n hn]
    rfl
  h₁ n hn := by
    rw [← Category.assoc, NatTrans.comp_app, H.h₁ n hn]
    rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy export _root_.SerrePositivity.KST.ProExcision.LinearizedMHomotopy (postcomp)

/-- 概要：幾何的な射がテンソル区間に誘導する射。
方針：自由化した射に区間の恒等射をテンソルする。
規約：KST Definition A.3。使われ方：A.5 の最後の対角による前合成。 -/
def linearizedCylinderMap (p : X ⟶ Y) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinder X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinder Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap p) (𝟙 _)

/-- 概要：零端点は幾何的な射に自然。
方針：自由加群の基底を零頂点との純テンソルへ送る。
規約：KST A.5。使われ方：前合成した比較の始点条件。 -/
lemma linearizedEndpoint₀_naturality (p : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₀ Y = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₀ X ≫ linearizedCylinderMap p := by
  apply NatTrans.ext
  funext n
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_hom_ext
  intro x
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₀ Y).app n
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map (p.app n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator, linearizedEndpoint₀_generator]
  change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map (p.app n)) (𝟙 _)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₀ X).app n (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x))
  rw [linearizedEndpoint₀_generator]
  change _ = TensorProduct.tmul ℤ
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map (p.app n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x)) _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator]
  rfl

/-- 概要：一端点は幾何的な射に自然。
方針：自由加群の基底を一頂点との純テンソルへ送る。
規約：KST A.5。使われ方：前合成した比較の終点条件。 -/
lemma linearizedEndpoint₁_naturality (p : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₁ Y = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₁ X ≫ linearizedCylinderMap p := by
  apply NatTrans.ext
  funext n
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_hom_ext
  intro x
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₁ Y).app n
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map (p.app n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator, linearizedEndpoint₁_generator]
  change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map (p.app n)) (𝟙 _)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₁ X).app n (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x))
  rw [linearizedEndpoint₁_generator]
  change _ = TensorProduct.tmul ℤ
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map (p.app n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x)) _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator]
  rfl

/-- 概要：m 次ホモトピーは始域の幾何的写像で引き戻せる。
方針：テンソル区間の誘導射を前合成し、端点の自然性を使う。
規約：KST A.5、最後の対角 T→T×T への引き戻し。
使われ方：二つの独立した入力の比較を同じ T 上の比較へ戻す。 -/
def LinearizedMHomotopy.precomp {f g : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace Y ⟶ D}
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy f g m) (p : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap p ≫ f) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap p ≫ g) m where
  h := linearizedCylinderMap p ≫ H.h
  h₀ n hn := by
    rw [← Category.assoc, ← linearizedEndpoint₀_naturality, Category.assoc,
      NatTrans.comp_app, H.h₀ n hn]
    rfl
  h₁ n hn := by
    rw [← Category.assoc, ← linearizedEndpoint₁_naturality, Category.assoc,
      NatTrans.comp_app, H.h₁ n hn]
    rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy export _root_.SerrePositivity.KST.ProExcision.LinearizedMHomotopy (precomp)

end SerrePositivity.KST.ProExcision
