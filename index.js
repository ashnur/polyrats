void function(root){
    "use strict"

    var pns = {}
        , u = require('totemizer')
        , V = require('momentum')
        , viral = require('viral')
        , R = V.r
        , ONE = R(1)
        , ZERO = R(0)
        ;


    function lefttrim(arr, maxDrop){
        if ( maxDrop == null ) maxDrop = arr.length-1
        while ( arr.length > 1 && arr[0] === ZERO && maxDrop > 0 ) {
            arr.shift()
            maxDrop--
        }
        return arr
    }

    function righttrim(arr){
        while ( arr.length > 1 && arr[arr.length-1] === ZERO  ) {
            arr.pop()
        }
        return arr
    }

    function largestNonZeroIndex(arr){
        var len = arr.length-1
        while( len > 0 && arr[len].compareAbs(ZERO) == 0 ) { len -= 1 }
        return len > -1 ? len : undefined
    }

    function alpha(pow){
        pow = pow == null ? 1 : pow
        var a=[], i = pow;
        while ( i-- > 0 ) { a.push(ZERO) }
        a.push(ONE)
        return a
    }

    function rand(max, min){
        var r =  Math.floor(Math.random() * (max - min + 1)) + min;
        return  r == 0 ?  rand(max, min) : r
    }

    function rndp(mindeg, maxdeg, pure){
        pure = pure != null ? false : pure

        var deg = rand(maxdeg == null ? 6 : maxdeg, mindeg == null ? 3 : mindeg)
            , base = alpha(deg)
            , common_factor = rand(13, -13)
            ;

        return piper(base.map(function(){
            var coefficient = rand(13, -13);
            return pure ? coefficient : coefficient * common_factor
        }))
    }

    function degree(arr){
        if ( arr && arr.init == polyrat.init ) {
            var numerator_degree = largestNonZeroIndex(arr[0])
            var denominator_degree = largestNonZeroIndex(arr[1])
            return numerator_degree > denominator_degree
                                ? numerator_degree
                                : denominator_degree
        } else if ( Array.isArray(arr) ) {
            return largestNonZeroIndex(arr)
        } else {
            throw new Error('Can not calculate degree')
        }
    }


    function divide(a, b){
        var remainder, divisor, k, j, quotient=[]
            , adeg = degree(a), bdeg = degree(b)
            ;

        remainder = a.slice(0)
        divisor = b.slice(0)

        for ( k = adeg - bdeg ; k >= 0 ; k-- ) {
            //quotient[k] = Math.floor(remainder[bdeg+k]/divisor[bdeg])
            quotient[k] = remainder[bdeg+k].divide(divisor[bdeg])
            for ( j = bdeg + k  ; j >= k ; j-- ) {
                remainder[j] = remainder[j].subtract(quotient[k].multiply(divisor[j-k]))
            }
        }

        quotient = righttrim(quotient)
        remainder = righttrim(remainder)


        return [quotient, remainder]
    }


    function gcd(a, b){
        var result = []
            , i = 1
            , deg_current , deg_last
            , lead_current , lead_last
            , divisor
            , shifts = [[0],[0]]
            , gcd
            ;
        // if any of the elements is 1, return 1 imediatelly
        if ( (a.length == 1 && a[0] == ONE) || (b.length == 1 && b[0] == ONE) ) {
            return piper([ONE])
        }
        // current element should be the smaller one
        // last element should be the larger one
        if ( degree(a) >= degree(b) ) {
            result[0] = a
            result[1] = b
        } else {
            result[0] = b
            result[1] = a
        }
        while ( ! result[i].every(function(c){ return c == ZERO }) ) {
            // degrees of the last and the current elements
            deg_last = degree(result[i-1])
            deg_current = degree(result[i])

            // raise the current element to the same power as the last element
            result[i] = piper(result[i]).times(piper(alpha(deg_last-deg_current)))[0]
            shifts[i%2].push(deg_last-deg_current)

            // get the leading coefficient for the last and current element
            lead_last = result[i-1][result[i-1].length-1]
            lead_current = result[i][result[i].length-1]

            // multiply the last and current element with the lead coefficients
            result[i-1] = V.scale(result[i-1], lead_current)
            result[i] = V.scale(result[i], lead_last)

            // calculate the gcd of all the coefficients from the elements
            divisor = V.gcd(result[i].concat(result[i-1]))

            // divide the last two elements with the gcd
            result[i-1] = V.disperse(result[i-1], divisor)
            result[i] = V.disperse(result[i], divisor)

            // calculate the difference between the last and current elements and
            // drop off the highest power, now zero coefficients
            result[i+1] = righttrim(V.sub(result[i-1], result[i]))

            i++

            // if we are past 2 iterations and nothing changed
            // there is no gcd, return 1

            if ( result.length > 3
                && piper(result[i]) == piper(result[i-2])
                && piper(result[i-1]) == piper(result[i-3])
               ) {
                return piper([ONE])
            }
        }
        // drop off all the smaller coefficients of 0 which
        // were introduced by raising
        return piper(lefttrim(result[i-1], shifts[(i-1)%2].reduce(function(x,y){return x+y})))
    }

    function hashify(p){
        return '['+p[0].join(',')+']/['+p[1].join(',')+']'
    }

    function display(p){
        //R display el van baszodva
        return degree(p) === 0
                ? p[0][0].per(p[1][0]).display()
                : '['+p[0].join(',')+']/['+p[1].join(',')+']'
    }

    function toPolynom(α){
        α = α == null ? 'α' : α
        function nom(v){
            return v.map(function(c,i){
                var O, C, B, P, ac = Math.abs(c);
                O =  ( i == v.length-1 || ac == 0 ) ? '' : c < 0 ? '-' : '+'
                C = ( ac == 0 || ( i > 0 && ac == 1 ) ) ? '' : ac
                B = ( i == 0 || ac == 0 ) ? '' : (ac == 1 ? '' : '*')+α
                P = (i == 0 || i == 1 || ac == 0) ? '' : '^'+i
                return O + C + B + P
            }).join('')
        }
        return '('+nom(this[0])+')/('+nom(this[1])+')'
    }

    function plus(first, second){
        var len, i, left, right, result=[];

        len = first.length > second.length ? first.length : second.length

        for ( i = 0; i < len; i++ ) {
            left = first[i] !== undefined ? first[i] : ZERO
            right = second[i] !== undefined ? second[i] : ZERO
            result[i] = left.add(right)
        }
        return result
    }

    function minus(first, second){
        var len, i, left, right, result=[];
        len = first.length > second.length ? first.length : second.length
        for ( i = 0; i < len; i++ ) {
            left = first[i] !== undefined ? first[i] : ZERO
            right = second[i] !== undefined ? second[i] : ZERO
            result[i] = left.minus(right)
        }
        return result
    }

    function times(first, second){
        var p, plen, q, qlen, i, j, result=[];
        p = first.slice(0)
        plen = first.length
        q = second.slice(0)
        qlen = second.length
        for ( i=0; i<plen; i++ ) {
            for ( j=0; j<qlen; j++ ) {
                if ( result[i+j] === undefined ) result[i+j] = ZERO
                if ( p[i+j] === undefined ) p[i+j] = ZERO
                if ( q[i+j] === undefined ) q[i+j] = ZERO
                result[i+j] = result[i+j].add(p[i].multiply(q[j]))
            }
        }
        return result
    }

    function per(first, second){
        var result

        if ( first.init == polyrat.init && second.init == polyrat.init ) {
            result = divide(first, second)
        } else {
            result = piper(first, second)
        }
        return result
    }

    function pow(first, second){
        var i, result=[];
        if ( ! u.isInt( second ) ) {
            throw new Error('undefined operation, look for roots elsewhere')
        }
        i=0
        result = first
        if ( second !== 0 ) {
            while ( ++i < second ) {
                result = result.times(first)
            }
        } else {
            result = piper([1])
        }
        return result
    }

    function val(first, second){
        var n = piper([0])
            , d = piper([0])
            , len
            , i
            , t1
            , t2
            ;
        if ( ! ( second && second.init == polyrat.init ) ) {
            if ( Array.isArray(second) ) {
                second = piper(second)
            } else {
                second = piper([second])
            }
        }
        len = first[0].length
        for ( i=0; i < len; i++ ) {
            t1 = piper([first[0][i]])
            t2 = piper(second.pow(i))
            n = n.plus(t1.times(t2))
        }
        len = first[1].length
        for ( i=0; i < len; i++ ) {
            t1 = piper([first[1][i]])
            t2 = piper(second.pow(i))
            d = d.plus(t1.times(t2))
        }
        return piper(n, d)
    }

    function plusMethod(a, b){
        var p = a[0]
            , q = a[1]
            , r = b[0]
            , s = b[1]
            ;
        return per(plus(times(p, s), times(r, q)), times(q, s))
    }

    function minusMethod(a, b){
        var q = a[1], s = b[1]
        return per(minus(times(a[0], s), times(b[0], q)), times(q, s))
    }
    function timesMethod(a, b){

        var p = a[0]
            , q = a[1]
            , r = b[0]
            , s = b[1]
            , n = times(p, r)
            , d = times(q, s)
            ;

        return per(n, d)
    }

    function perMethod(a, b){
        var p = a[0]
            , q = a[1]
            , r = b[0]
            , s = b[1]
            , n = times(p, s)
            , d = times(r, q)
            ;

        return per(n, d)
    }

    function leftTranslate(a, b){
        return val(a, piper([b,ONE]))
    }

    var polyrat = viral.extend({
        init: function(idx, n, d){
            this[0] = n
            this[1] = d
        }
        , hashify: u.enslave(display)
        , toString: u.enslave(display)
        , display: u.enslave(display)
        , toPolynom: u.enslave(toPolynom)
        , degree: u.enslave(degree)
        , pow: u.enslave(pow)
        , val: u.enslave(val)
        , times: u.enslave(timesMethod)
        , plus: u.enslave(plusMethod)
        , minus: u.enslave(minusMethod)
        , per: u.enslave(perMethod)
        , divide: u.enslave(divide)
        , leftTr: u.enslave(leftTranslate)
        //, compose: u.enslave(compose)
    })


    function piper(numerator, denominator){
        var key, idx, t, len, i, j, dd, divisor

        if ( numerator && numerator.init ==  polyrat.init ) {
            if ( denominator == null ) {
                return numerator
            } else if ( denominator && denominator.init == polyrat.init) {
                var n = times(numerator[0], denominator[1])
                var d = times(denominator[0], numerator[1])
                numerator = n
                denominator = d
            }
        }

        if ( ! Array.isArray(numerator) ) {
            throw new Error('invalid argument, array expected instead of '+
                    numerator+' ('+typeof numerator+')')
        } else {
            numerator = V(numerator)
        }

        denominator = Array.isArray(denominator) ? V(denominator) : [ONE]

        numerator = righttrim(numerator)
        denominator = righttrim(denominator)

        dd = largestNonZeroIndex(denominator)

        if ( dd  === undefined ) {
            throw new Error('the denominator must not equal 0')
        }

        if ( dd > 0 ) {
            divisor = gcd(numerator, denominator)
            if ( degree(divisor[0]) > 0 || divisor[0][0] !== ONE ) {
                numerator = divide(numerator, divisor[0])[0]
                denominator = divide(denominator, divisor[0])[0]
            }
        }

        if ( numerator.length === 1 && numerator[0] === ZERO ) {
            denominator = [ONE]
        }

        divisor = V.gcd(numerator.concat(denominator))

        divisor = denominator[denominator.length-1].multiply(divisor).compare(ZERO) == -1
                                            ? divisor.times(R(-1))
                                            : divisor


        // scale down both vectors with the divisor
        numerator = righttrim(V.disperse(numerator, divisor))
        denominator = righttrim(V.disperse(denominator, divisor))

        idx = '['+numerator.join(',')+']/['+denominator.join(',')+']'

        if ( pns[idx] === undefined ) {
            pns[idx] = polyrat.make(idx, numerator, denominator)
        }


        return pns[idx]
    }

    piper.polyrat = polyrat

    piper.rndp = rndp

    if ( module != undefined && module.exports ) {
        module.exports = piper
    } else {
        root.factory = piper
    }

}(this)
