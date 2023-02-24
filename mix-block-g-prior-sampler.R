library(invgamma)
library(WoodburyMatrix)
library(mvtnorm)
library(truncnorm)
library(extraDistr)
resample <- function(x, ...) x[sample.int(length(x), ...)]

# Taken from here :  https://github.com/willtownes/mit6882/blob/master/will/speed_tests.Rmd
# Some discussion here:  http://www.statsathome.com/2018/10/19/sampling-from-multivariate-normal-precision-and-covariance-parameterizations/
custom4<-function(n,theta,Lambda,D=length(theta)){
  Q<-chol(Lambda)
  Z<-matrix(rnorm(n*D),nrow=D,ncol=n)
  #using vector recycling tricks below
  #Q^{-1}*Z+Lambda^{-1}*theta == Q^{-1}*(Z+(Q')^{-1}*theta)
  backsolve(Q,Z+drop(backsolve(Q,theta,transpose=TRUE)))
}

rhyperg <- function(n,a){
  h <- rbeta(n,1,a/2-1)
  return(h/(1-h))
}

rhypergn <- function(x,a,n){
  h <- rbeta(x,1,a/2-1)
  return(n*h/(1-h))
}


rtgamma <- function(n, shape, rate, truncation){
  # Sampling fron truncated gamma involves three steps:
  
  # 1) Find the probability corresponding to truncation point 
  p_trunc = pgamma(truncation, shape = shape, rate = rate)
  # 2) Draw from uniform distribution with max = the probability of truncation point
  u_trucgam <- runif(n,0, p_trunc)
  # 3) Draw quantile corresponding to u_truncgam from the inverse gamma distribution
  t <- qgamma(u_trucgam,shape = shape, rate = rate)
  
  return(t)
}
#### Proposal function for gamma variable ####
proposal.gamma <- function(gam, d=4){
  p <- length(gam)
  prob1 <- c(0.4,0.3,0.2,0.1)#c(0.5,0.3,0.15,0.05)
  prob2 <- c(0.7,0.3)
  
  s <- resample(1:2,1, prob = prob2)
  # Use technique of George mchlloch stat sinaca paper  eq 46 if s==1
  
  if(s==1){
    if(p<d){
      d=p
      prob1 <- prob1[1:d]/sum(prob1[1:d])
    }
    d0 <- resample(1:d,1, prob=prob1)
    ind <- resample(1:p,d0)
    gam[ind]=!gam[ind]
    
    
    # swap one entry from active set with one entry from non-active set randomly
  }else if(s==2){
    if(all(gam==1)){
      ind <- resample(1:p,1)
      gam[ind]=0
    }else if(all(gam==0)){
      ind <- resample(1:p,1)
      gam[ind]=1
    }else{
      gam1 <- which(gam==1)
      gam0 <- which(gam==0)
      ind1 <- resample(gam1,1)
      ind0 <- resample(gam0,1)
      gam[ind1] <- 0
      gam[ind0] <- 1
    }
  }
  return(gam)
}


to_right_Matrix <- function(x) {
  symmetric <- FALSE
  if (is(x, 'diagonalMatrix')) {
    x
  } else {
    as(x, if (symmetric) 'symmetricMatrix' else 'Matrix')
  }
}

log_marginal <- function(x,y,g,gam,hyper.prior){
  
  n <- length(y)
  p <- ncol(x)
  #print(sum(gam))
  x <-  x[ ,as.logical(gam)]
  g <- g[as.logical(gam)]
  pgam <- sum(gam)
  if(length(g)==0){
    # Do calculation as if X and G are not there
    xtx <- xty <- g <-  NULL
    num1 <- sum((y-mean(y))^2)
    logmg <- lgamma((n-1)/2) - 0.5*log(n) - 
      0.5*(n-1)*log(pi)-0.5*(n-1)*log(num1)
  }else{
    # Calculate using our formula
    xtx <- t(x)%*% x
    xty <- t(x)%*% y
    
    if(hyper.prior=="beta-prime-MG"){
      ghalf <- diag(sqrt(g),nrow = pgam,ncol=pgam)
      xghalf <- x %*% ghalf
      mat <- WoodburyMatrix(A=diag(n), X= xghalf, B=xtx)
    }else{
      ghalf.inv <- diag(1/sqrt(g),nrow = pgam,ncol=pgam)
      # print(paste("min:",min(g)))
      # print(paste("max:",max(g)))
      gxtxg <- ghalf.inv %*% xtx %*% ghalf.inv
      gxtxg <- (gxtxg+t(gxtxg))/2
      # temp <- solve(xtx+gxtxg)
      # print(isSymmetric(temp))
      # B_parts <- if (!is.list(gxtxg)) list(gxtxg) else gxtxg
      # B_parts <- lapply(B_parts, to_right_Matrix)
      # print(gxtxg)
      # print("Done this calculation")
      mat <- WoodburyMatrix(A=diag(n), X= x , B=gxtxg)
      
    }
    
    # g_025 <- diag((g)^{0.25},nrow = pgam,ncol=pgam)
    # g_025_inv <- diag((g)^{-0.25},nrow = pgam,ncol=pgam)
    # mat <- WoodburyMatrix(A=diag(n), X= x %*% g_025, B= g_025_inv %*% xtx %*% g_025_inv)
    
    
    num1 <- as.numeric(y%*% solve(mat) %*% y - n*mean(y)^2)
    den <- as.numeric(determinant(mat, logarithm = TRUE)$modulus)
    logmg <- lgamma((n-1)/2) - 0.5*log(n) - 
      0.5*(n-1)*log(pi)-0.5*(n-1)*log(num1)-0.5*den
  }
  
  res <- list("logmg"=logmg, "xtx"=xtx, "xty"=xty, "ggam"=g, "sig2rate"=num1)
  return(res)
}


#### Algorithm 1 of Liu et al 2013 ####
gamma_rejection_sampler <- function(alpha, gam_param,truncation=NULL){
  if(is.null(truncation)){
    if(gam_param<=0){
      logdelta0 <- log(4*alpha)-2*log(sqrt(gam_param^2+4*alpha)+abs(gam_param))
      delta0 <- exp(logdelta0)
      
      t <- rgamma(1,shape = alpha, rate = delta0)
      u <- runif(1) # MADE A CHANGE IN WHILE CONDITION extra alpha 
      while (log(u) > alpha -t*(1-delta0)-2*sqrt(t)*gam_param-alpha/delta0){
        t <- rgamma(1,shape = alpha, rate = delta0)
        u <- runif(1)
      }
    }else{
      t <- rgamma(1,alpha,1)
      u <- runif(1) # log(u) > -2gamma*sqrt(t)
      while (log(u)> -2*gam_param*sqrt(t)) {
        t <- rgamma(1,alpha,1)
        u <- runif(1)
      }
    }
    
  }else{
    if(gam_param<=0){
      logdelta0 <- log(4*alpha)-2*log(sqrt(gam_param^2+4*alpha)+abs(gam_param))
      delta0 <- exp(logdelta0)
      
      t <- rtgamma(1,shape = alpha, rate = delta0,truncation = truncation)
      u <- runif(1) # made a change here in while loop
      while (log(u) > alpha-t*(1-delta0)-2*sqrt(t)*gam_param-alpha/delta0){
        t <- rtgamma(1,shape = alpha, rate = delta0,truncation = truncation)
        u <- runif(1)
      }
    }else{
      t <- rtgamma(1,shape=alpha,rate=1,truncation = truncation)
      u <- runif(1) # made a change here in while loop condition
      while (log(u)> -2*gam_param*sqrt(t)) {
        t <- rtgamma(1,shape=alpha,rate=1,truncation=truncation)
        u <- runif(1)
      }
    }
    
  }
  return(t)
}

#### Algorithm 2 of Liu et al 2013 ####
normal_rejection_sampler <- function(alpha,gam_param,truncation=NULL){
  if(alpha<1/2){
    stop("For normal RS, alpha needs to be greater than 1/2")
  }
  
  if(alpha==1/2){
    m <- max(-gam_param,0)
  }else{
    logm <- log(2*alpha-1)-log(gam_param+sqrt(gam_param^2+4*alpha-2))
    m <- exp(logm)
  }
  
  if(is.null(truncation)){
    x <- rtruncnorm(1,mean=m,sd=1/sqrt(2),a=0)
    u <- runif(1)
    while ((2*alpha-1)*log(m)+ log(u) >(2*alpha-1)*log(x)-2*(m+gam_param)*(x-m)) {
      x <- rtruncnorm(1,mean=m,sd=1/sqrt(2),a=0)
      u <- runif(1)
    }
  }else{
    x <- rtruncnorm(1,mean=m,sd=1/sqrt(2),a=0, b=sqrt(truncation))
    u <- runif(1)
    while ((2*alpha-1)*log(m)+ log(u) > (2*alpha-1)*log(x)-2*(m+gam_param)*(x-m)) {
      x <- rtruncnorm(1,mean=m,sd=1/sqrt(2),a=0, b=sqrt(truncation))
      u <- runif(1)
      #print(x)
    }
    
  }
  return(x^2)
}


# Algorithm 3 of Liu et al 2013 ####
gamma_rs_sqrt_scale <- function(alpha, gam_param,truncation=NULL){
  if(alpha<0){
    stop("For gamma RS on sqrt scale, alpha >0")
  }
  delta1 <- gam_param+sqrt(gam_param^2+4*alpha)
  r <- 2*alpha
  
  if(is.null(truncation)){
    x <- rgamma(1,r,delta1)
    u <- runif(1)
    while (log(u)>-(x-(delta1/2-gam_param))^2) {
      x <- rgamma(1,r,delta1)
      u <- runif(1)
    }
  }else{
    x <- rtgamma(1,shape=r,rate=delta1,truncation = sqrt(truncation))
    u <- runif(1)
    while (log(u)>-(x-(delta1/2-gam_param))^2) {
      x <- rtgamma(1,shape=r,rate=delta1,truncation = sqrt(truncation))
      u <- runif(1)
    }
    
  }
  return(x^2)
}

#### Optimal Rejection sampler for extended gamma distribution (Liu el al 2013) ####
ext_gamma_sampler <- function(alpha, gam_param,truncation=NULL){
  if(gam_param !=0){
    logC <- log(abs(gam_param)) - 0.5*log(alpha)
    C <- sign(gam_param)*exp(logC)
  }else if(gam_param==0){
    C <- 0
  }
  # C <- gam_param/sqrt(alpha)
  # if(abs(gam_param)<10^{-3}|abs(gam_param)>10^3){
  #   print(paste("gam_param:", gam_param))
  # }
  if(C<= -0.7){
    z <- normal_rejection_sampler(alpha,gam_param,truncation)
  }else if (-0.7 < C & C < 0.7){
    z <- gamma_rejection_sampler(alpha,gam_param,truncation)
  }else if (C >= 0.7){
    z <- gamma_rs_sqrt_scale(alpha,gam_param,truncation)
  }
  return(z)
}

#### main function ####
Blockg.lm <- function(x,y,
                      grp_idx=NULL,
                      burn=10000,
                      nmc=9000,
                      thinning=10, 
                      model.prior="beta-binomial",
                      hyper.prior="Inv-gamma", # "hyper-g", "hyper-g-n",
                      # "beta-prime-MG","beta-prime"
                      hyper.param=NULL){
  
  n <- length(y)
  p <- ncol(x)
  
  if(!is.null(grp_idx)){
    #Store useful quantites
    grp_size <- as.vector(table(grp_idx))
    grp_size_cs <- cumsum(grp_size)
    group_ids = unique(grp_idx)
    K = length(group_ids)
    
    if(length(grp_idx) != p) {
      stop("The argument grp_idx must have length p, where p in the number of columns in X.")
    }
    
    if(any(diff(group_ids) > 1)) {
      stop("Groups skip a number somewhere in grp_idx. Ensure that grp_idx is an ordered sequence
         from 1 to p with no skips. A valid example is 1,1,1,2,2,3,3,3,4,5,5.")
    }
  }
  
  
  #### Conditions/ tests on priors specified ####
  if(hyper.prior=="Inv-gamma"){
    if(is.null(hyper.param)){
      a1 <- 1/2
      a2 <- n/2
    }
    if(length(hyper.param)==2){
      if(hyper.param[1]>0 & hyper.param[2]>0){
        a1=hyper.param[1]
        a2=hyper.param[2]
      }else{
        stop("Inv-gamma requires a and b >0")
      }
    }
    if(length(hyper.param)>2| length(hyper.param)==1){
      stop("Inv-gamma specification requires only two 
           hyper-parameters which are both >0")
    }
  }
  
  if(hyper.prior=="hyper-g"){
    if(is.null(hyper.param)){a=3
    }else{
      if(length(hyper.param)>1| (hyper.param!=3 & hyper.param!=4)){
        stop("Hyper-g requires just one hyper parameter with recommended value 3 or 4")}
    }
    
  }
  if(hyper.prior=="hyper-g-n"){
    if(is.null(hyper.param)){
      a=3
    }else{
      if(length(hyper.param)>1| (hyper.param!=3 & hyper.param!=4)){
        stop("Hyper-g/n requires just one hyper 
                         parameter with value 3 or 4")}
      
    }
  }
  if(hyper.prior=="beta-prime-MG"){
    if(is.null(hyper.param)){
      a=-3/4
    }else{
      if(length(hyper.param)>1){
        stop("Maryuma and George recommended a to be between -1 and -1/2 and b to be adaptive")
      }
      if(!(-1< hyper.param & hyper.param< -1/2)){
        stop("Maryuma and George recommended a to be between -1 and -1/2")}
      
    }
  }
  if(hyper.prior=="beta-prime"){
    if(is.null(hyper.param)){
      a=-0.5
      b_param=-0.5
    }
    if(length(hyper.param)==2){
      if(hyper.param[1]>-1 & hyper.param[2]>-1){
        a=hyper.param[1]
        b_param=hyper.param[2]
      }else{
        stop("Beta-prime specification requires a and b >-1")
      }
    }
    if(length(hyper.param)>2| length(hyper.param)==1){
      stop("Beta-prime specification requires only two 
           hyper-parameters which are both >-1")
    }
  }
  
  #### Initialization ####
  # create matrix to save variables
  GammaSave = matrix(NA, nmc, p)
  BetaSave = matrix(NA, nmc, p+1)
  Sigma2Save <- matrix(NA, nmc, 1)
  logBF212Save <- matrix(NA,nmc,1)
  logmargSave <- matrix(NA,nmc,1)
  gvalSave <- matrix(NA, nmc, p)
  timemat <- matrix(NA, nmc*thinning+burn, 4)
  xtx.full <- t(x)%*% x
  # Intialize parameters
  gam = rep(0,p)
  alpha <- mean(y)
  b <- rep(0, p)
  g.old <- n
  g_K <- rep(g.old,K)
  g <- rep(g.old, p)#rinvgamma(p, 1/2, n/2)
  sigma2 <- 1
  
  
  #### MCMC Iteration loop ####
  for(t in 1:(nmc*thinning+burn)){
    
    if (t%%1000 == 0){cat(paste(t," "))}
    
    #### Update Gamma####
    start_time <- Sys.time()
    # Propose gamma
    gam.prop <- proposal.gamma(gam)
    
    if(sum(gam.prop)< n-1){
      logmarg.prop.obj <- log_marginal(x,y,g,gam.prop,hyper.prior=hyper.prior)
    }
    logmarg.curr.obj <- log_marginal(x,y,g, gam,hyper.prior=hyper.prior)
    # Calculate acceptance probability for (gam.prop,delta.cand)
    
    if(p==2){
      m2 <- c(1,1)
      m1 <- c(1,0)
      logmarg.m2.obj <- log_marginal(x,y,g,m2)
      logmarg.m1.obj <- log_marginal(x,y,g,m1)
      logbf21 <- logmarg.m2.obj$logmg - (logmarg.m1.obj$logmg)
    }else{
      logbf21 <- NA
    }
    
    
    # under beta-binomial
    if(model.prior=="beta-binomial"){
      if(sum(gam.prop)<n-1){
        oj.num.log <- -lchoose(p,sum(gam.prop)) + logmarg.prop.obj$logmg  
      }else{
        oj.num.log <- -Inf
      }
      oj.den.log <-  -lchoose(p,sum(gam))+logmarg.curr.obj$logmg
      
      # logbf21 <- logmarg.m2.obj$logmg - (logmarg.m1.obj$logmg)
    }else if (model.prior=="Uniform"){ # Under Uniform model prior
      # define oj.num.log and oj.den.log
      if(sum(gam.prop)<n-1){
        oj.num.log <- logmarg.prop.obj$logmg  
      }else{
        oj.num.log <- -Inf
      }
      
      oj.den.log <- logmarg.curr.obj$logmg
      # logbf21 <- logmarg.m2.obj$logmg - logmarg.m1.obj$logmg
    }
    
    u.gam <- runif(1)
    
    #print(paste("Iteration",t,":", as.numeric(exp(oj.num.log-oj.den.log)),sep = ""))  
    
    
    #print(oj.den.log)
    loga.gam.prob <- min(as.numeric(oj.num.log-oj.den.log),0)
    if(log(u.gam)<=loga.gam.prob){
      gam <- gam.prop
      xtx <- logmarg.prop.obj$xtx
      xty <- logmarg.prop.obj$xty
      ggam <- logmarg.prop.obj$ggam
      sig2rate <- logmarg.prop.obj$sig2rate
      logmarg <- logmarg.prop.obj$logmg
    }else{
      gam <- gam
      xtx <- logmarg.curr.obj$xtx
      xty <- logmarg.curr.obj$xty
      ggam <- logmarg.curr.obj$ggam
      sig2rate <- logmarg.curr.obj$sig2rate
      logmarg <- logmarg.curr.obj$logmg
      
    }
    end_time <- Sys.time()
    timemat[t,1] <- end_time-start_time
    
    
    #### Update alpha and Beta #####
    start_time <- Sys.time()
    
    alpha <- rnorm(1, mean(y), sqrt(sigma2/n))
    pgam <- sum(gam)
    
    if(is.null(xtx)){
      b <- rep(0,p)
    }else{
      ggam_inv_half <- diag(1/sqrt(ggam),nrow = pgam,ncol = pgam) 
      #print(min(ggam))
      #print(max(ggam))
      prec.mat <- ggam_inv_half %*% xtx %*% ggam_inv_half + xtx
      # covariance matrix is inverse of 1/sigma2*prec.mat and 
      # mean is cov matrix multiplied by xty/sigma^2 so that sigma2 cancel out in mean
      b <- custom4(1,1/sigma2*xty,1/sigma2*prec.mat)
      # cov.mat <- solve(prec.mat)
      # post.mean <- cov.mat%*% xty
      # b <- rmvnorm(1, post.mean, sigma2*cov.mat)
    }
    
    end_time <- Sys.time()
    timemat[t,2] <- end_time-start_time
    
    
    #### Update sigma2 ####
    start_time <- Sys.time()
    
    sigma2 <- rinvgamma(1, (n-1)/2, sig2rate/2)
    
    timemat[t,3] <- end_time-start_time
    
    #### Update g ####
    start_time <- Sys.time()
    pgam <- sum(gam)
    
    if(is.null(xtx)){
      C <- NULL
    }else{
      bvec <- as.vector(b)
      bvec.full <- rep(0,p)
      bvec.full[which(gam==1)] <- bvec
      C <- (2*sigma2)^{-1}* diag(bvec.full,nrow=length(bvec.full),ncol = length(bvec.full)) %*% xtx.full %*% 
        diag(bvec.full, nrow=length(bvec.full),ncol = length(bvec.full))
    }

    for(k in 1:K){
      grp_mem <- which(grp_idx==k)
      grp_mem_in_mod <- which(grp_idx==k & gam==1)
      s_k <- length(grp_mem_in_mod)
      if(s_k!=0){
        p_k <- length(grp_mem_in_mod)
        #print(pgam)
        #print((grp_mem_in_mod))
        #print((C))
        
        if(pgam==p_k){
            c_k <- sum(C)
            d_k <- 0
        }else{
          c_k <- sum(C[grp_mem_in_mod,grp_mem_in_mod])
          d_k <- sum(2*C[grp_mem_in_mod,-grp_mem_in_mod]%*%(1/sqrt(g[-grp_mem_in_mod])))
        }
        
        # sample g_k from that distribution using slice + rejection sampling
        if(hyper.prior=="Inv-gamma"){
          # draw from an extended Gamma distribution
          gam_prime <- d_k/(2*sqrt(c_k+a2))
          gk_inv <- ext_gamma_sampler(alpha = a1+p_k/2, gam_param = 
                                       gam_prime,truncation = NULL)
          gk_inv <- gk_inv/(c_k+a2)
          g_K[k] <- 1/gk_inv
          g[grp_mem] <- 1/gk_inv
        }else if(hyper.prior=="hyper-g"){
          t_i <- 1/g_K[k] # Think about it carefully g or g_gam
          #print(t_i)
          # Slice sampling approach
          ht_i <- (1+t_i)^{-a/2}
          u_i <- runif(1,0,ht_i)
          truncation <- c_k*(u_i^{-2/a}-1)
          zeta <- d_k/(2*sqrt(c_k))
          #print(d_k)
          #print(c_k)
          #print(zeta)
          z_i <- ext_gamma_sampler(alpha = (a+p_k-2)/2,gam_param = zeta,
                                   truncation = truncation)
          gk_inv <- z_i/c_k
          g_K[k] <- 1/gk_inv
          g[grp_mem] <- 1/gk_inv
          
        }else if(hyper.prior=="hyper-g-n"){
          t_i <- 1/g_K[k] 
          # Slice sampling approach
          ht_i <- (1+n*t_i)^{-a/2}
          u_i <- runif(1,0,ht_i)
          truncation <- c_k*1/n*(u_i^{-2/a}-1)
          zeta <- d_k/(2*sqrt(c_k))
          z_i <- ext_gamma_sampler(alpha = (a+p_k-2)/2,gam_param = zeta,
                                   truncation = truncation)
          gk_inv <- z_i/c_k
          g_K[k] <- 1/gk_inv
          g[grp_mem] <- 1/gk_inv
        }else if(hyper.prior=="beta-prime"|hyper.prior=="beta-prime-MG"){
          t_i <- 1/g_K[k] 
          
          # Slice sampling approach
          pgam <- sum(gam)
          if(hyper.prior=="beta-prime-MG"){
            b_param <- (n-pgam-5)/2 -a
          }else if(hyper.prior=="beta-prime"){
            b_param <- b_param
          }
          #print(paste("Cii:",C[count,count]))
          #print(paste("di:",d_i))
          if(c_k==0 & d_k==0){
            bp.tran <- rbeta(1,a+p_k/2+1,b_param+1-p_k/2)
            g[ind] <- exp(log(bp.tran)-log(1-bp.tran))
          }else{
            ht_i <- (1+t_i)^{-(a+b_param+2)}#{-(n-pgam-1)/2}
            u_i <- runif(1,0,ht_i)
            truncation <- c_k*(u_i^{-1/(a+b_param+2)}-1)#(u_i^{-2/(n-pgam-1)}-1)
            zeta <- d_k/(2*sqrt(c_k))
            # if(abs(zeta)>10^5 | is.nan(zeta)){
            #   print(pgam)
            #   print(count)
            #   print(paste("g_i:",ggam[count]))
            #   print(paste("b_i:",bvec[count]))
            #   print(paste("xtxii:",xtx[count,count]))
            #   print(paste("Cii:",C[count,count]))
            #   print(paste("di:", d_i))
            # }
            z_i <- ext_gamma_sampler(alpha = a+p_k/2+1,gam_param = zeta,
                                     truncation = truncation)
            gk_inv <- z_i/c_k
            g_K[k] <- 1/gk_inv
            g[grp_mem] <- 1/gk_inv
          }
      }}else{
        # sample g_k from prior distribution
        if(hyper.prior=="Inv-gamma"){
          g_K[k] <- rinvgamma(1,a1,a2) 
        }else if(hyper.prior=="hyper-g"){
          g_K[k] <- rhyperg(1,a)
        }else if(hyper.prior=="hyper-g-n"){
          g_K[k] <- rhypergn(1,a,n)
        }else if(hyper.prior=="beta-prime"|hyper.prior=="beta-prime-MG"){
          if(hyper.prior=="beta-prime"){
            b_param <- b_param
          }else if(hyper.prior=="beta-prime-MG"){
            b_param <- (n-pgam-5)/2 -a
          }
          bp.tran <- rbeta(1,a+1,b_param+1)
          g_K[k] <- exp(log(bp.tran)-log(1-bp.tran))#rbetapr(1, a+1, b_param+1)
        }
        if(length(grp_mem)!=0){
          g[grp_mem] <- g_K[k]
        }
      }
    }
    
    end_time <- Sys.time()
    timemat[t,4] <- end_time-start_time
    
    betastore=rep(0,p)
    #Save results post burn-in
    if(t > burn && (t - burn) %% thinning == 0){
      rr  <- floor((t - burn) / thinning)
      GammaSave[rr, ] = gam
      # count3=1
      # gam.withintercept <- c(1,gam)
      # betastore[1] <- alpha
      # for (k in 2:(p+1)){
      #   if(gam.withintercept[k]==1){
      #     betastore[k]= b[count3]
      #     count3=count3+1
      #   }
      # }
      betastore[which(gam==1)] <- b
      betastore <- c(alpha,betastore)
      BetaSave[rr, ] = betastore
      Sigma2Save[rr, ] <- sigma2
      logmargSave[rr, ] <- logmarg
      gvalSave[rr, ] <- g
      logBF212Save[rr, ] <- logbf21
    }
  }
  
  # Store results as a list
  result <- list("BetaSamples"=BetaSave,
                 "GammaSamples"=GammaSave,
                 "Sigma2Samples"=Sigma2Save,
                 "gsamples"=gvalSave,
                 "logBF21"=logBF212Save,
                 "timemat"=timemat)
  # Return object
  return(result)
  
}


