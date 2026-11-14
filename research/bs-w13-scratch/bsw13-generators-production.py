from pathlib import Path
tmp=Path('/tmp/bsw13-kernel-probe.lean').read_text()
body=tmp[tmp.index('include hR in\nprivate theorem annihilator_isModuleComplete'):]
body=body.replace('end SerrePositivity.BhattScholze.Almost\n\nnamespace SerrePositivity.BhattScholze.Almost\nopen CategoryTheory SerrePositivity.DerivedCompletion SerrePositivity.InfinityCategories\nattribute [local instance] HasDerivedCategory.standard\nset_option backward.isDefEq.respectTransparency false\n\nvariable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)\n\ndef isPCompleteVertex (M : DVertex R) : Prop :=\n  IsComplete R (p : R) ((derivedInfinityHomotopyEquivalence R).functor.obj ⟨M⟩)\n\n','')
body='\n'.join(line for line in body.splitlines() if not line.startswith('#print axioms'))+'\n'
body=body.replace('theorem isAlmostZero_perfectoidKernel_sup', '''/-- 二つの核による almost 零性を、その和のイデアルの almost 零性にまとめる。 -/
theorem isAlmostZero_perfectoidKernel_sup''')
body=body.replace('theorem isAlmostZero_iff_forall_gen', '''/--
## 概要
有限生成イデアルによる almost 零性を生成元ごとに判定する。
BS 著者版 Theorem 10.9 の証明の主イデアルへの帰着で使う。

## 方針
コホモロジー加群の零化イデアルで割り、perfectoid な二つの商の完備テンソルを使う。

## 規約
コホモロジー次数を用いる。生成族が空の場合を含む。

## 使われ方
BS 著者版 Remark 10.7 に続く almost 零性の比較。
-/
theorem isAlmostZero_iff_forall_gen''')
body=body.replace('simpa only [Finset.coe_empty, Ideal.span_empty, SerrePositivity.Almost.IsAlmostZero] using',
    'simpa only [Finset.coe_empty, Ideal.span_empty,\n          SerrePositivity.Almost.IsAlmostZero] using')
body=body.replace('(h : perfectoidKernel p R hR J ≤ RingHom.ker (algebraMap R A)) :', '(h : perfectoidKernel p R hR J ≤ RingHom.ker (algebraMap R A)) :')
body=body.replace('change Ideal.Quotient.lift (perfectoidKernel p R hR J) (algebraMap R A) (fun _ hx ↦ h hx)',
    'change Ideal.Quotient.lift (perfectoidKernel p R hR J) (algebraMap R A)\n      (fun _ hx ↦ h hx)')
body=body.replace('\n\n\n','\n\n')
header='''module

public import SerrePositivity.BhattScholze.Almost.AlmostConnectivity
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.IntegralPerfectoid

/-! # 生成元ごとの almost 零性

## 概要
BS 著者版 Theorem 10.9 の証明に使う有限生成イデアルの almost 零性の判定。

## 方針
零化イデアルによる導来完備な商へ、二つの perfectoid 商の完備テンソルから写す。

## 規約
複体は導来 p 完備、各次数の零化は通常の加群の零化。

## 使われ方
almost purity の主イデアルへの帰着。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.BhattScholze.Almost
open CategoryTheory CategoryTheory.Limits DerivedCompletion InfinityCategories
open Perfectoidization.Derived
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)

'''
Path('/tmp/BSW13AlmostGenerators.lean').write_text(header+body)
q=Path('/tmp/BSW13AlmostConnectivity.lean')
s=q.read_text()
s+='''

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived
open CategoryTheory InfinityCategories DerivedCompletion
open scoped Simplicial
attribute [local instance] HasDerivedCategory.standard

/-- 頂点を通常の導来圏に移し、主元 p に関する導来完備性を判定する。 -/
def isPCompleteVertex (p : ℕ) (R : Type u) [CommRing R]
    (M : (derivedInfinityCategory R) _⦋0⦌) : Prop :=
  IsComplete R (p : R) ((derivedInfinityHomotopyEquivalence R).functor.obj ⟨M⟩)

end SerrePositivity.BhattScholze.Perfectoidization.Derived
'''
q.write_text(s)
